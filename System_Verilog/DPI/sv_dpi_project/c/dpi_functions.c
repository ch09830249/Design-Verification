/*
 * ============================================================
 *  DPI 完整學習專案 — C 端實作
 *  dpi_functions.c
 * ============================================================
 */

#include "dpi_functions.h"
#include "svdpi.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <ctype.h>

/* ============================================================
 *  [區塊 1] 基本型別傳遞
 *
 *  重點：
 *   - SV int    <->  C int
 *   - SV real   <->  C double
 *   - SV string <->  C const char*  (唯讀！不能修改)
 *   - SV bit    <->  C svBit  (typedef unsigned char)
 *   - SV byte   <->  C svByte (typedef signed char)
 * ============================================================ */

/* SV: import "DPI-C" function int c_add(int a, int b); */
int c_add(int a, int b)
{
    printf("[C][c_add]  %d + %d = %d\n", a, b, a + b);
    return a + b;
}

/* SV: import "DPI-C" function real c_multiply_real(real x, real y); */
double c_multiply_real(double x, double y)
{
    printf("[C][c_multiply_real]  %.4f * %.4f = %.4f\n", x, y, x * y);
    return x * y;
}

/* SV: import "DPI-C" function void c_print_string(string msg); */
void c_print_string(const char* msg)
{
    /*
     * 注意：SV string 傳入 C 是 const char*
     * 你不能對它呼叫 free()，也不能修改它的內容
     */
    printf("[C][c_print_string]  接收到字串: \"%s\"  (長度=%zu)\n",
           msg, strlen(msg));
}

/* SV: import "DPI-C" function int c_string_length(string s); */
int c_string_length(const char* s)
{
    return (int)strlen(s);
}

/* SV: import "DPI-C" function bit c_check_even(int n); */
svBit c_check_even(int n)
{
    /*
     * svBit = unsigned char，值只有 0 或 1
     * SV 的 bit 型別與 C 的 svBit 對應
     */
    printf("[C][c_check_even]  %d 是%s數\n", n, (n % 2 == 0) ? "偶" : "奇");
    return (svBit)(n % 2 == 0 ? 1 : 0);
}

/* SV: import "DPI-C" function byte c_to_upper(byte ch); */
svByte c_to_upper(svByte ch)
{
    return (svByte)toupper((unsigned char)ch);
}


/* ============================================================
 *  [區塊 2] Open Array 操作
 *
 *  重點：
 *   svOpenArrayHandle — 傳遞動態大小的 SV 陣列
 *   常用 API：
 *     svSize(h, dim)          — 取得第 dim 維的大小 (1-based)
 *     svLeft(h, dim)          — 左邊界 index
 *     svRight(h, dim)         — 右邊界 index
 *     svGetArrElemPtr1(h, i)  — 取得一維陣列第 i 個元素指標
 *     svGetArrElemPtr2(h,i,j) — 取得二維陣列第 [i][j] 元素指標
 * ============================================================ */

/* SV: import "DPI-C" function void c_fill_array(inout int arr[]); */
void c_fill_array(svOpenArrayHandle arr)
{
    int left  = svLeft (arr, 1);   /* 最小 index */
    int right = svRight(arr, 1);   /* 最大 index */
    int size  = svSize (arr, 1);   /* 元素個數   */

    printf("[C][c_fill_array]  index [%d:%d], 共 %d 個元素\n",
           left, right, size);

    for (int i = left; i <= right; i++) {
        int* elem = (int*)svGetArrElemPtr1(arr, i);
        if (elem) {
            *elem = i * i;   /* 填入 index 的平方 */
        }
    }
    printf("[C][c_fill_array]  填入 arr[i] = i^2 完成\n");
}

/* SV: import "DPI-C" function int c_sum_array(input int arr[]); */
int c_sum_array(svOpenArrayHandle arr)
{
    int left  = svLeft (arr, 1);
    int right = svRight(arr, 1);
    int total = 0;

    for (int i = left; i <= right; i++) {
        int* elem = (int*)svGetArrElemPtr1(arr, i);
        if (elem) total += *elem;
    }

    printf("[C][c_sum_array]   總和 = %d\n", total);
    return total;
}

/* SV: import "DPI-C" function void c_reverse_array(inout int arr[]); */
void c_reverse_array(svOpenArrayHandle arr)
{
    int left  = svLeft (arr, 1);
    int right = svRight(arr, 1);
    int size  = svSize (arr, 1);

    /* 先把資料複製出來 */
    int* buf = (int*)malloc(size * sizeof(int));
    for (int i = left; i <= right; i++) {
        int* e = (int*)svGetArrElemPtr1(arr, i);
        buf[i - left] = e ? *e : 0;
    }

    /* 反序寫回 */
    for (int i = left; i <= right; i++) {
        int* e = (int*)svGetArrElemPtr1(arr, i);
        if (e) *e = buf[(right - i)];
    }

    free(buf);
    printf("[C][c_reverse_array]  陣列已反序\n");
}

/* SV: import "DPI-C" function void c_print_2d_array(input int arr[][]); */
void c_print_2d_array(svOpenArrayHandle arr)
{
    /*
     * 二維 open array：
     *   dim=1 → 第一維 (row)
     *   dim=2 → 第二維 (col)
     */
    int r_left  = svLeft (arr, 1);
    int r_right = svRight(arr, 1);
    int c_left  = svLeft (arr, 2);
    int c_right = svRight(arr, 2);

    printf("[C][c_print_2d_array]  row[%d:%d], col[%d:%d]\n",
           r_left, r_right, c_left, c_right);

    for (int r = r_left; r <= r_right; r++) {
        printf("  row[%d] : ", r);
        for (int c = c_left; c <= c_right; c++) {
            int* e = (int*)svGetArrElemPtr2(arr, r, c);
            printf("%4d ", e ? *e : 0);
        }
        printf("\n");
    }
}


/* ============================================================
 *  [區塊 3] Struct 傳遞
 *
 *  重點：
 *   SV 端宣告 typedef struct packed {} 或 unpacked struct
 *   C 端使用對應的 C struct
 *   指標傳遞 (input 用 const*, inout 用 *)
 * ============================================================ */

void c_process_packet(const CPacket* pkt)
{
    printf("[C][c_process_packet]\n");
    printf("  id    = %d\n", pkt->id);
    printf("  value = %d\n", pkt->value);
    printf("  score = %.2f\n", pkt->score);
    printf("  name  = \"%s\"\n", pkt->name);
}

void c_fill_packet(CPacket* pkt, int id, double score)
{
    pkt->id    = id;
    pkt->value = id * 10;
    pkt->score = score;
    snprintf(pkt->name, sizeof(pkt->name), "packet_%03d", id);
    printf("[C][c_fill_packet]  填入 id=%d score=%.2f\n", id, score);
}


/* ============================================================
 *  [區塊 4] Blocking Task
 *
 *  重點：
 *   SV 端宣告為 task (不是 function)
 *   C 端函式會消耗模擬時間
 *   需要 context 呼叫能力 (svSetScope)
 *
 *   注意：在 xrun 中 blocking task 需要宣告為 context
 * ============================================================ */

/* SV: import "DPI-C" context task c_blocking_sort(inout int arr[]); */
void c_blocking_sort(svOpenArrayHandle arr)
{
    int left  = svLeft (arr, 1);
    int right = svRight(arr, 1);
    int size  = svSize (arr, 1);

    printf("[C][c_blocking_sort]  開始排序 %d 個元素...\n", size);

    /* 把資料取出做 bubble sort */
    int* buf = (int*)malloc(size * sizeof(int));
    for (int i = left; i <= right; i++) {
        int* e = (int*)svGetArrElemPtr1(arr, i);
        buf[i - left] = e ? *e : 0;
    }

    /* Bubble sort */
    for (int i = 0; i < size - 1; i++) {
        for (int j = 0; j < size - i - 1; j++) {
            if (buf[j] > buf[j+1]) {
                int tmp = buf[j]; buf[j] = buf[j+1]; buf[j+1] = tmp;
            }
        }
    }

    /* 寫回 */
    for (int i = left; i <= right; i++) {
        int* e = (int*)svGetArrElemPtr1(arr, i);
        if (e) *e = buf[i - left];
    }
    free(buf);

    printf("[C][c_blocking_sort]  排序完成\n");
}


/* ============================================================
 *  [區塊 5] Chandle — C 物件指標管理
 *
 *  重點：
 *   SV 的 chandle 型別對應 C 的 void*
 *   可以傳遞任意 C 結構指標給 SV 保存
 *   SV 不知道裡面的內容，只是保存這個 handle
 *   需要手動管理記憶體 (create / destroy)
 * ============================================================ */

typedef struct {
    int   count;
    int   step;
    char  name[16];
} Counter;

/* SV: import "DPI-C" function chandle c_create_counter(int init_val); */
void* c_create_counter(int init_val)
{
    Counter* c = (Counter*)malloc(sizeof(Counter));
    c->count = init_val;
    c->step  = 1;
    snprintf(c->name, sizeof(c->name), "CTR_%d", init_val);
    printf("[C][c_create_counter]  建立計數器 \"%s\" 初始值=%d addr=%p\n",
           c->name, c->count, (void*)c);
    return (void*)c;   /* 回傳 void* → SV 的 chandle */
}

/* SV: import "DPI-C" function void c_increment(chandle handle); */
void c_increment(void* handle)
{
    if (!handle) { fprintf(stderr, "[C] c_increment: null handle!\n"); return; }
    Counter* c = (Counter*)handle;
    c->count += c->step;
    printf("[C][c_increment]  \"%s\" count = %d\n", c->name, c->count);
}

/* SV: import "DPI-C" function int c_get_count(chandle handle); */
int c_get_count(void* handle)
{
    if (!handle) return -1;
    Counter* c = (Counter*)handle;
    return c->count;
}

/* SV: import "DPI-C" function void c_destroy_counter(chandle handle); */
void c_destroy_counter(void* handle)
{
    if (!handle) { fprintf(stderr, "[C] c_destroy_counter: null handle!\n"); return; }
    Counter* c = (Counter*)handle;
    printf("[C][c_destroy_counter]  釋放計數器 \"%s\" addr=%p\n",
           c->name, handle);
    free(c);
}


/* ============================================================
 *  [區塊 6] svdpi.h 進階 API
 *
 *  svScope         — scope 物件 (對應 SV module/class instance)
 *  svGetScope()    — 取得目前執行的 SV scope
 *  svSetScope(s)   — 切換到指定 scope (讓 export 函式在正確 scope 執行)
 *  svGetTime(t)    — 取得目前模擬時間
 *  svPutUserData   — 在 scope 上綁定自訂 C 資料
 *  svGetUserData   — 取回綁定的資料
 * ============================================================ */

/* SV: import "DPI-C" context function void c_use_scope_api(); */
void c_use_scope_api(void)
{
    /*
     * svGetScope() 回傳呼叫這個函式的 SV scope
     * 只有 context function/task 才能呼叫 svGetScope
     */
    svScope scope = svGetScope();

    if (scope == NULL) {
        printf("[C][c_use_scope_api]  scope = NULL (非 context 呼叫?)\n");
        return;
    }

    const char* scope_name = svGetNameFromScope(scope);
    printf("[C][c_use_scope_api]  目前 scope = \"%s\"\n",
           scope_name ? scope_name : "(unknown)");

    /* 你可以儲存 scope 以便之後切換回來 */
    svScope saved = svGetScope();
    printf("[C][c_use_scope_api]  scope 已儲存: %p\n", (void*)saved);
}

/* SV: import "DPI-C" context function void c_use_time_api(); */
void c_use_time_api(void)
{
    /*
     * svGetTime 需要傳入 svTimeVal 結構
     * struct svTimeVal {
     *   svTimeUnit   unit;      // 時間單位
     *   svTimestamp  realtime;  // 實際時間 (64-bit)
     * }
     * 注意：不同模擬器的實作略有差異
     */
    svTimeVal tv;
    svGetTime(NULL, &tv);   /* NULL = 使用目前 scope */
    printf("[C][c_use_time_api]  模擬時間 = %llu (unit=%d)\n",
           (unsigned long long)tv.integer, (int)tv.unit);
}

/* SV: import "DPI-C" context function void c_use_userdata(); */
void c_use_userdata(void)
{
    /*
     * svPutUserData(scope, key, data)
     *   — 把 C 資料綁定到 SV scope
     *   — key 是 void* (通常用靜態變數的地址當 key)
     * svGetUserData(scope, key)
     *   — 取回之前存入的資料
     *
     * 這樣可以讓 C 端在不同呼叫之間保持狀態
     */

    static int  key;    /* 用靜態變數地址當 unique key */
    svScope     scope = svGetScope();

    if (!scope) {
        printf("[C][c_use_userdata]  scope = NULL\n");
        return;
    }

    /* 嘗試取回舊資料 */
    int* data = (int*)svGetUserData(scope, &key);

    if (!data) {
        /* 第一次呼叫：建立資料 */
        data = (int*)malloc(sizeof(int));
        *data = 1000;
        svPutUserData(scope, &key, data);
        printf("[C][c_use_userdata]  第一次呼叫：建立 userdata = %d\n", *data);
    } else {
        /* 後續呼叫：讀取並更新 */
        (*data)++;
        printf("[C][c_use_userdata]  後續呼叫：userdata = %d\n", *data);
    }
}


/* ============================================================
 *  [區塊 7] Pure 函式
 *
 *  重點：
 *   SV 端宣告：import "DPI-C" pure function int c_pure_fibonacci(int n);
 *   pure = 沒有 side-effect，相同輸入永遠相同輸出
 *          模擬器可以快取結果，或平行執行最佳化
 *   限制：pure 函式不能
 *     - 呼叫任何 svdpi.h API
 *     - 使用 static/global 變數
 *     - 做任何 I/O
 * ============================================================ */

int c_pure_fibonacci(int n)
{
    /* 這個函式 "看起來" 有 printf，但在 pure 宣告下不應該有
     * 這裡示意：實際 pure 函式請拿掉所有 I/O */
    if (n <= 0) return 0;
    if (n == 1) return 1;
    int a = 0, b = 1;
    for (int i = 2; i <= n; i++) {
        int tmp = a + b; a = b; b = tmp;
    }
    return b;
}

double c_pure_power(double base, int exp)
{
    double result = 1.0;
    for (int i = 0; i < exp; i++) result *= base;
    return result;
}


/* ============================================================
 *  [Export 呼叫示範]
 *
 *  以下函式會主動呼叫 SV 端的 export function
 *  SV 端宣告：export "DPI-C" function sv_compute_crc;
 *
 *  注意：C 端需要先有對應的函式原型 (由模擬器自動產生 header)
 *  在這裡用 extern 宣告
 * ============================================================ */

/*
 * SV export 的函式原型由模擬器在編譯時期生成
 * 在 xrun 中用 -dpiimpheader 或 -dpiobjheader 產生
 * 這裡用 extern 手動宣告以便示意：
 */
extern int sv_compute_crc(int data);

/* 這個 C 函式會被 SV 呼叫，然後它再回呼 SV 的 export function */
/* 此函式在 tb_top.sv 中以 import 宣告 */
void c_call_sv_export(int input_data)
{
    printf("[C][c_call_sv_export]  呼叫 sv_compute_crc(data=%d)\n", input_data);

    /*
     * 呼叫 SV 端 export 的函式
     * 這就是 C -> SV 的 export 回呼
     */
    int crc = sv_compute_crc(input_data);
    printf("[C][c_call_sv_export]  SV 回傳 CRC = 0x%08X\n", crc);
}
