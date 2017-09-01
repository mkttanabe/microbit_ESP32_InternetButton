/*
 * microbit_ESP32_01.c
 *
 * for ESP-IDF
 *
 * use BBC micro:bit as "Internet Buttons".
 *
 *        [micro:bit]                      [ESP-WROOM-32]
 *  button A -> send BLE packet A  =>  BLE recv -> call Web API A
 *  button B -> send BLE packet B  =>  BLE recv -> call Web API B
 *
 *
 * This code is based on the official sample code below.
 *
 *  https://github.com/espressif/esp-idf/tree/master/examples/bluetooth/gatt_client
 *  https://www.esp32.com/viewtopic.php?t=984
 *
 * 2017-08 KLab Inc.
 *
 */
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stdbool.h>
#include <stdlib.h>

#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "freertos/event_groups.h"
#include "esp_wifi.h"
#include "esp_event_loop.h"
#include "esp_log.h"
#include "esp_system.h"
#include "nvs_flash.h"

#include "lwip/err.h"
#include "lwip/sockets.h"
#include "lwip/sys.h"
#include "lwip/netdb.h"
#include "lwip/dns.h"

#include "mbedtls/platform.h"
#include "mbedtls/net.h"
#include "mbedtls/debug.h"
#include "mbedtls/ssl.h"
#include "mbedtls/entropy.h"
#include "mbedtls/ctr_drbg.h"
#include "mbedtls/error.h"

#include "controller.h"
#include "bt.h"
#include "bt_trace.h"
#include "bt_types.h"
#include "btm_api.h"
#include "bta_api.h"
#include "esp_gap_ble_api.h"
#include "esp_bt_main.h"

//#define DEVELOP
#ifdef DEVELOP
#define _LOGI(tag, format, ...) ESP_LOGI(tag, format, ##__VA_ARGS__)
#else
#define _LOGI(tag, format, ...)
#endif
#define _LOGE(tag, format, ...) ESP_LOGE(tag, format, ##__VA_ARGS__)
#define _LOGW(tag, format, ...) ESP_LOGW(tag, format, ##__VA_ARGS__)

#ifdef TAG
#undef TAG
#endif
#define TAG "mb"
#define TAG_BLE  TAG " [BLE]"
#define TAG_INET TAG " [INET]"

// LED ports
#define PORT_LED_GREEN  GPIO_NUM_2
#define PORT_LED_RED    GPIO_NUM_17

// for WiFi AP
#define EXAMPLE_WIFI_SSID "ssid"
#define EXAMPLE_WIFI_PASS "password"

// FreeRTOS event group to signal when we are connected & ready to make a request
static EventGroupHandle_t inet_event_group;
static const int CONNECTED_BIT = BIT0; // status of AP connection
static const int REQUEST_BIT   = BIT1; // status of new HTTP request

// Eddystone 16-bit UUID
// https://github.com/google/eddystone/blob/master/implementations/mbed/source/EddystoneTypes.h
static const uint8_t EDDYSTONE_UUID[] = {0xAA, 0xFE};

// The byte ID of an Eddystone-URL frame
// https://github.com/google/eddystone/blob/master/implementations/mbed/source/URLFrame.h
static const uint8_t FRAME_TYPE_URL = 0x10;

// BLE scanner parameters
static esp_ble_scan_params_t ble_scan_params = {
    .scan_type              = BLE_SCAN_TYPE_ACTIVE,
    .own_addr_type          = BLE_ADDR_TYPE_PUBLIC,//ESP_PUBLIC_ADDR,
    .scan_filter_policy     = BLE_SCAN_FILTER_ALLOW_ALL,
    .scan_interval          = 0x50,
    .scan_window            = 0x30
};

// table of targets
typedef struct {
    esp_bd_addr_t macAddr;      // MAC address
    uint8_t id;                 // button id
    uint8_t isQueued;           // queue flag for HTTP request
    unsigned long lastExecTime; // last requested time
    char url[256];              // request URL
} TARGET_ENTRY;

#define NUM_ENTRIES 2

static TARGET_ENTRY Entries[NUM_ENTRIES] = {
    {{0xf2, 0x1d, 0xa9, 0x78, 0xdf, 0x2b}, // micro:bit 1
    'A', // Button A
    0,
    ULONG_MAX, 
    "https://prod-05.japaneast.logic.azure.com/workflows/******"
    },
    {{0xf2, 0x1d, 0xa9, 0x78, 0xdf, 0x2b}, // micro:bit 1
    'B',// Button B
    0,
    ULONG_MAX, 
    "https://prod-08.japaneast.logic.azure.com/workflows/******"
    }
};

static TARGET_ENTRY *pCurrentTargetEntry = NULL;

static void alert(uint32_t count)
{
    uint32_t n = (count <= 0) ? UINT32_MAX : count;
    for (uint32_t i = 0; i < n; i++) {
        gpio_set_level(PORT_LED_RED, 0);
        vTaskDelay(500 / portTICK_PERIOD_MS);
        gpio_set_level(PORT_LED_RED, 1);
        vTaskDelay(1000 / portTICK_PERIOD_MS);
    }
}

// BLE GAP event handler
static void esp_gap_cb(esp_gap_ble_cb_event_t event, esp_ble_gap_cb_param_t *param)
{
    esp_bd_addr_t mac;
    uint8_t value_len, *value;

    switch (event) {
    case ESP_GAP_BLE_SCAN_PARAM_SET_COMPLETE_EVT: {
        //the unit of the duration is second
        uint32_t duration = UINT32_MAX; // 4294967295 secs
        esp_ble_gap_start_scanning(duration);
        break;
    }
    case ESP_GAP_BLE_SCAN_START_COMPLETE_EVT:
        //scan start complete event to indicate scan start successfully or failed
        if (param->scan_start_cmpl.status != ESP_BT_STATUS_SUCCESS) {
            _LOGE(TAG_BLE, "Scan start failed");
        }
        break;

     case ESP_GAP_BLE_SEC_REQ_EVT:
        // send the positive(true) security response to the peer device to accept the security request.
        // If not accept the security request, should sent the security response with negative(false) accept value
        esp_ble_gap_security_rsp(param->ble_security.ble_req.bd_addr, true);
        break;

    // When one scan result ready, the event comes each time 
    case ESP_GAP_BLE_SCAN_RESULT_EVT: {
        esp_ble_gap_cb_param_t *scan_result = (esp_ble_gap_cb_param_t *)param;

        switch (scan_result->scan_rst.search_evt) {
        // Inquiry result for a peer device. 
        case ESP_GAP_SEARCH_INQ_RES_EVT:
            // MAC address
            memcpy(mac, scan_result->scan_rst.bda, ESP_BD_ADDR_LEN);
            _LOGI(TAG_BLE, "time=%lu, found: MAC addr=[%02x:%02x:%02x:%02x:%02x:%02x]",
                time(NULL), mac[0],mac[1],mac[2],mac[3],mac[4],mac[5]);

            // 1. is Eddystone packet?
            // ESP_BLE_AD_TYPE_16SRV_CMPL = 0x03
            // sample: 0x03 0xAAFE
            value = esp_ble_resolve_adv_data(scan_result->scan_rst.ble_adv,
                                ESP_BLE_AD_TYPE_16SRV_CMPL, &value_len);
            if (value_len != 2 || memcmp(value, EDDYSTONE_UUID, 2) != 0) {
                break;
            }

            // 2. Get button id from Eddystone-URL frame
            // (e.g.: "http://A" -> id="A", "http://B" -> id="B")

            // https://github.com/google/eddystone/blob/master/protocol-specification.md
            //
            // Eddystone Protocol Specification
            // Frame Byte Value
            // UID   0x00
            // URL   0x10
            //      :
            //
            // https://github.com/google/eddystone/tree/master/eddystone-url
            //
            // Eddystone-URL
            //
            // Frame Specification
            // Byte offset Field        Description
            //          0  Frame Type   Value = 0x10
            //          1  TX Power     Calibrated Tx power at 0 m
            //          2  URL Scheme   Encoded Scheme Prefix
            //          3+ Encoded URL  Length 1-17
            //
            // URL Scheme Prefix
            // Decimal   Hex  Expansion
            //      0   0x00  http://www.
            //      1   0x01  https://www.
            //      2   0x02  http://
            //      3   0x03  https://

            // ESP_BLE_AD_TYPE_SERVICE_DATA = 0x16,
            // sample: 0x16 0xAAFE 0x10F60242
            //               -> 10:type URL F6:-10dBm 02:"http://" 42:'B'
            value = esp_ble_resolve_adv_data(scan_result->scan_rst.ble_adv,
                                ESP_BLE_AD_TYPE_SERVICE_DATA, &value_len);
            if (value_len != 6 || memcmp(value, EDDYSTONE_UUID, 2) != 0 ||
                value[2] != FRAME_TYPE_URL) {
                break;
            }
            uint8_t id = value[5];

            // 3. check target entries
            for (int i = 0; i < NUM_ENTRIES; i++) {
                // MAC address + button id is matched
                if (memcmp(scan_result->scan_rst.bda, 
                    Entries[i].macAddr, ESP_BD_ADDR_LEN) == 0 &&
                    id == Entries[i].id) {
                    if (Entries[i].isQueued != 1) {
                        // 10 seconds or more is needed after the last request
                        unsigned long t = time(NULL);
                        if (Entries[i].lastExecTime == ULONG_MAX ||
                            t - Entries[i].lastExecTime >= 10) {
                            _LOGI(TAG_BLE, "** START **");
                            // set queue flag for HttpsRequestTask
                            Entries[i].isQueued = 1;
                        } else {
                            _LOGI(TAG_BLE, "found, pending..");
                        }
                    }
                }
            }
            break;

        case ESP_GAP_SEARCH_INQ_CMPL_EVT:
            break;

        default:
            break;
        }
        break;
    }
    default:
        break;
    }
}

// start BLE scanner
static void start_ble_central()
{
    esp_err_t status;
    esp_bt_controller_config_t bt_cfg = BT_CONTROLLER_INIT_CONFIG_DEFAULT();
    esp_bt_controller_init(&bt_cfg);
    esp_bt_controller_enable(ESP_BT_MODE_BTDM);

    esp_bluedroid_init();
    esp_bluedroid_enable();

    //register the scan callback function to the gap moudule
    _LOGI(TAG_BLE, "register BLE callback..");
    if ((status = esp_ble_gap_register_callback(esp_gap_cb)) != ESP_OK) {
        _LOGE(TAG_BLE, "gap register error, error code=|%x", status);
        return;
    }
    esp_ble_gap_set_scan_params(&ble_scan_params);
}

// WiFi event handler
static esp_err_t wifi_event_handler(void *ctx, system_event_t *event)
{
    _LOGI(TAG_INET, "wifi_event_handler id=%d(0x%x)", event->event_id, event->event_id);
    switch(event->event_id) {
    case SYSTEM_EVENT_STA_START:
        esp_wifi_connect();
        break;
    case SYSTEM_EVENT_STA_GOT_IP:
        xEventGroupSetBits(inet_event_group, CONNECTED_BIT);
        break;
    case SYSTEM_EVENT_STA_DISCONNECTED:
        // This is a workaround as ESP32 WiFi libs don't currently
        // auto-reassociate. */
        esp_wifi_connect();
        xEventGroupClearBits(inet_event_group, CONNECTED_BIT);
        break;
    default:
        break;
    }
    return ESP_OK;
}

// init WiFi 
static void initWifi(void)
{
    tcpip_adapter_init();
    inet_event_group = xEventGroupCreate();
    ESP_ERROR_CHECK(esp_event_loop_init(wifi_event_handler, NULL) );
    wifi_init_config_t cfg = WIFI_INIT_CONFIG_DEFAULT();
    ESP_ERROR_CHECK( esp_wifi_init(&cfg) );
    ESP_ERROR_CHECK( esp_wifi_set_storage(WIFI_STORAGE_RAM) );
    wifi_config_t wifi_config = {
        .sta = {
            .ssid = EXAMPLE_WIFI_SSID,
            .password = EXAMPLE_WIFI_PASS,
        },
    };
    _LOGI(TAG_INET, "Setting WiFi configuration SSID %s...", wifi_config.sta.ssid);
    ESP_ERROR_CHECK( esp_wifi_set_mode(WIFI_MODE_STA) );
    ESP_ERROR_CHECK( esp_wifi_set_config(ESP_IF_WIFI_STA, &wifi_config) );
    ESP_ERROR_CHECK( esp_wifi_start() );
}

// get hostname from an URL
// https://www.example.com/hogehoge/... -> "www.example.com"
static char *getHostNameFromUrl(const char *url, char *outBuf, int outBufLength)
{
    char *p1, *p2;
    if (!url || !outBuf || outBufLength <= 0) {
        return NULL;
    }
    if (!(p1 = strstr(url, "//"))) {
        return NULL;
    }
    p1 += 2;
    if (!(p2 = strchr(p1, ':'))) {
        if (!(p2 = strchr(p1, '/'))) {
            return NULL;
        }
    }
    int len = p2 - p1;
    if (len >= outBufLength) {
        return NULL;
    }
    strncpy(outBuf, p1, len);
    outBuf[len] = '\0';
    _LOGI(TAG_INET, "host=[%s]", outBuf);
    return outBuf;
}

// task for HTTPS request & response
// based on https://www.esp32.com/viewtopic.php?t=984
static void httpsTask(void *p)
{
    int ret, len, retry;
    char host[64];
    char buf[512];
    mbedtls_entropy_context entropy;
    mbedtls_ctr_drbg_context ctr_drbg;
    mbedtls_ssl_context ssl;
    mbedtls_ssl_config conf;
    mbedtls_net_context server_fd;

    mbedtls_ssl_init(&ssl);
    mbedtls_ctr_drbg_init(&ctr_drbg);

    _LOGI(TAG_INET, "Seeding the random number generator");
    mbedtls_ssl_config_init(&conf);
    mbedtls_entropy_init(&entropy);
    if((ret = mbedtls_ctr_drbg_seed(&ctr_drbg,
                mbedtls_entropy_func, &entropy, NULL, 0)) != 0) {
        _LOGE(TAG_INET, "mbedtls_ctr_drbg_seed returned %d", ret);
        abort();
    }

    _LOGI(TAG_INET, "Setting up the SSL/TLS structure...");
    if((ret = mbedtls_ssl_config_defaults(&conf,
                        MBEDTLS_SSL_IS_CLIENT,
                        MBEDTLS_SSL_TRANSPORT_STREAM,
                        MBEDTLS_SSL_PRESET_DEFAULT)) != 0) {
        _LOGE(TAG_INET, "mbedtls_ssl_config_defaults returned %d", ret);
        goto exit;
    }

    mbedtls_ssl_conf_authmode(&conf, MBEDTLS_SSL_VERIFY_NONE);
    mbedtls_ssl_conf_rng(&conf, mbedtls_ctr_drbg_random, &ctr_drbg);
    // set timeout to mbedtls_ssl_read()
    mbedtls_ssl_conf_read_timeout(&conf, 4000); // 4 second

    if ((ret = mbedtls_ssl_setup(&ssl, &conf)) != 0) {
        alert(0);
    }

    while (1) {
        // wait for CONNECTED_BIT
        xEventGroupWaitBits(inet_event_group, CONNECTED_BIT,
                            false, true, portMAX_DELAY);
        _LOGI(TAG_INET, "WiFi AP is available");

        // wait for REQUEST_BIT
        _LOGI(TAG_INET, "wait for request..");
        xEventGroupWaitBits(inet_event_group, REQUEST_BIT,
                            false, true, portMAX_DELAY);

        if (!pCurrentTargetEntry) {
            _LOGI(TAG_INET, "target entry is not found");
            xEventGroupClearBits(inet_event_group, REQUEST_BIT);
            continue;
        }

        getHostNameFromUrl(pCurrentTargetEntry->url, host, sizeof(host));

        mbedtls_net_init(&server_fd);

        retry = 3;
        _LOGI(TAG_INET, "Connecting to %s..", host);
        do {
            if ((ret = mbedtls_net_connect(&server_fd, host,
                                          "443", MBEDTLS_NET_PROTO_TCP)) != 0) {
                _LOGE(TAG_INET, "mbedtls_net_connect returned -%x,retrying..", -ret);
                vTaskDelay(2000 / portTICK_PERIOD_MS);
            } else {
                break;
            }
        } while (retry-- > 0);

        if (retry <= 0) {
            goto exit;
        }

        // enable mbedtls_ssl_conf_read_timeout()
        // https://tls.mbed.org/api/ssl_8h.html
        mbedtls_ssl_set_bio(&ssl, &server_fd, mbedtls_net_send,
                mbedtls_net_recv, mbedtls_net_recv_timeout);

        retry = 3;
        _LOGI(TAG_INET, "Performing the SSL/TLS handshake...");
        while ((ret = mbedtls_ssl_handshake(&ssl)) != 0) {
            if (ret != MBEDTLS_ERR_SSL_WANT_READ && ret != MBEDTLS_ERR_SSL_WANT_WRITE) {
                if (retry-- > 0) {
                    _LOGE(TAG_INET, "mbedtls_ssl_handshake returned -0x%x, retrying..", -ret);
                    vTaskDelay(1000 / portTICK_PERIOD_MS);
                    continue;
                } else {
                    goto exit;
                }
            }
        }

        snprintf(buf, sizeof(buf),
            "GET %s HTTP/1.1\nHost: %s\nUser-Agent: esp-idf/1.0 esp32\n\n",
                pCurrentTargetEntry->url, host);
        retry = 3;
        _LOGI(TAG_INET, "Writing HTTP request..");
        while((ret = mbedtls_ssl_write(&ssl, (const unsigned char *)buf, strlen(buf))) <= 0) {
            if(ret != MBEDTLS_ERR_SSL_WANT_READ && ret != MBEDTLS_ERR_SSL_WANT_WRITE) {
                if (retry-- > 0) {
                    _LOGE(TAG_INET, "mbedtls_ssl_write returned -0x%x, retrying..", -ret);
                    vTaskDelay(1000 / portTICK_PERIOD_MS);
                    continue;
                } else {
                    goto exit;
                }
            }
        }
        len = ret;
        _LOGI(TAG_INET, "%d bytes written", len);
        _LOGI(TAG_INET, "Reading HTTP response...");

        do {
            len = sizeof(buf) - 1;
            bzero(buf, sizeof(buf));
            _LOGI(TAG_INET, "wait for mbedtls_ssl_read");
            ret = mbedtls_ssl_read(&ssl, (unsigned char *)buf, len);

            if (ret == MBEDTLS_ERR_SSL_TIMEOUT) {
                _LOGI(TAG_INET, "mbedtls_ssl_read timeout");
                break;
            } else if (ret == MBEDTLS_ERR_SSL_WANT_READ ||
                ret == MBEDTLS_ERR_SSL_WANT_WRITE) {
                continue;
            } else if (ret == MBEDTLS_ERR_SSL_PEER_CLOSE_NOTIFY) {
                ret = 0;
                break;
            } else if (ret < 0) {
                _LOGE(TAG_INET, "mbedtls_ssl_read returned -0x%x", -ret);
                break;
            } else if (ret == 0) {
                _LOGI(TAG_INET, "connection closed");
                break;
            }
            len = ret;
            _LOGI(TAG_INET, "%d bytes read", len);

#ifdef DEVELOP
            // Print response directly to stdout as it is read
            for(int i = 0; i < len; i++) {
                putchar(buf[i]);
            }
#endif
        } while (1);

        mbedtls_ssl_close_notify(&ssl);
exit:
        mbedtls_ssl_session_reset(&ssl);
        mbedtls_net_free(&server_fd);

        if(ret != 0 && ret != MBEDTLS_ERR_SSL_TIMEOUT) {
            mbedtls_strerror(ret, buf, 100);
            if (ret != MBEDTLS_ERR_SSL_TIMEOUT) {
                gpio_set_level(PORT_LED_RED, 1);
                _LOGE(TAG_INET, "Last error was: -0x%x - %s", -ret, buf);
            }
        }
        // wait for next request
        _LOGI(TAG_INET, "clearing REQUEST_BIT");
        xEventGroupClearBits(inet_event_group, REQUEST_BIT);
    }
}

// wait for HttpsTask to become idle
static bool waitForHttpsTask(int timeoutSeconds)
{
    int retry = timeoutSeconds;
    do {
        EventBits_t uxBits = xEventGroupGetBits(inet_event_group);
        if (uxBits & REQUEST_BIT) {
            _LOGI(TAG_INET, "wait for HttpsTask..");
            vTaskDelay(1000 / portTICK_PERIOD_MS);
            retry--;
        } else {
            break;
        }
    } while (retry > 0);
    return (retry <= 0) ? false : true;
}

// request to HttpsTask
static void httpsRequestTask(void *p)
{
    while (1) {
        for (int i = 0; i < NUM_ENTRIES; i++) {
            if (Entries[i].isQueued == 1) {
                gpio_set_level(PORT_LED_GREEN, 1);
                bool sts = waitForHttpsTask(30);
                if (!sts) {
                    gpio_set_level(PORT_LED_RED, 1);
                    _LOGE(TAG,"requestToHttpsTask timeout!");
                } else {
                    pCurrentTargetEntry = &Entries[i];
                    // wake httpsTask
                    xEventGroupSetBits(inet_event_group, REQUEST_BIT);
                    // wait for finish 
                    sts = waitForHttpsTask(30);
                    if (!sts) {
                        xEventGroupClearBits(inet_event_group, REQUEST_BIT);
                    }
                }
                Entries[i].isQueued = 0;
                Entries[i].lastExecTime = time(NULL);
                pCurrentTargetEntry = NULL;
                gpio_set_level(PORT_LED_GREEN, 0);
            }
        }
        vTaskDelay(200 / portTICK_PERIOD_MS);
    }
}

static void heapCheckTask(void *p)
{
    while (1) {
        _LOGW(TAG, "heap=%d", esp_get_free_heap_size());
        vTaskDelay(20000 / portTICK_PERIOD_MS);
    }
}

#define TEST_RESTART
#ifdef  TEST_RESTART
static void restartTask(void *p)
{
    // memory leak suspicion in mbedtls..
    while (1) {
        vTaskDelay(3600000 / portTICK_PERIOD_MS);
        if (waitForHttpsTask(30)) {
            esp_restart();
        }
    }
}
#endif

void app_main()
{
    // for LED
    gpio_set_direction(PORT_LED_GREEN, GPIO_MODE_OUTPUT);
    gpio_set_level(PORT_LED_GREEN, 0);
    gpio_set_direction(PORT_LED_RED, GPIO_MODE_OUTPUT);
    gpio_set_level(PORT_LED_RED, 0);

    nvs_flash_init();
    initWifi();

    // create tasks
    xTaskCreate(&httpsTask, "https", 8192, NULL, 5, NULL);
    xTaskCreate(&httpsRequestTask, "req", 2048, NULL, 5, NULL);
    xTaskCreate(&heapCheckTask, "heap", 2048, NULL, tskIDLE_PRIORITY, NULL);
#ifdef TEST_RESTART
    xTaskCreate(&restartTask, "restart", 2048, NULL, tskIDLE_PRIORITY, NULL);
#endif

    // start BLE scanner
    start_ble_central();
}
