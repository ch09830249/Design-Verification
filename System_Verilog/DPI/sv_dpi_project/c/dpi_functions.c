/*
 * ============================================================
 *  DPI 完整學習專案 — C 端實作 (Final)
 *  dpi_functions.c
 *
 *  Xcelium 23.x svdpi.h 型別注意事項：
 *    svByte    → 不存在，改用 signed char（ABI 相同）
 *    svTimeVal → 不存在，改用「SV 端把 $time 傳進來」的模式
 *    svBit     → 存在，= unsigned char，值只有 0 或 1
 *
 *  函式分類：
 *    [1] 基本型別   int / double / string / svBit / signed char
 *    [2] Open Array svOpenArrayHandle + svLeft/svRight/svSize/svGetArrElemPtr
 *    [3] Struct     C struct 對應 SV typedef struct
 *    [4] Blocking   import task → C 函式回傳 int (0=ok, 1=disable)
 *    [5] Chandle    void* ↔ SV chandle，手動管理記憶體
 *    [6] svdpi API  svGetScope / svGetNameFromScope / svPutUserData / svGetUserData
 *    [7] Pure       無 side-effect，模擬器可快取/平行最佳化
 *    [8] Export     C 端呼叫 SV 定義的 export function
 * ============================================================
 */

#include "dpi_functions.h"
#include "svdpi.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <ctype.h>
#include <stdint.h>


/* ============================================================
 *  [區塊 1] 基本型別傳遞
 *
 *  SV ↔ C 型別對應表（Xcelium 23.x）：
 *
 *    SV 型別    C 型別          說明
 *    --------  --------------  ----------------------------
 *    int        int             32-bit 有號整數
 *    real       double          64-bit 浮點數
 *    string     const char*     唯讀！不能 free()，不能修改
 *    bit        svBit           = unsigned char，值 0 或 1
 *    byte       signed char     svdpi.h 裡沒有 svByte，
 *                               直接用 signed char，ABI 相同
 *    shortint   short           16-bit 整數
 *    longint    long long       64-bit 整數
 *    chandle    void*           不透明指標
 *
 *  傳遞方向：
 *    input  → C 端收到值（或 const 指標），不能修改原始資料
 *    output → C 端透過指標寫回結果
 *    inout  → C 端既能讀也能寫，改動反映回 SV
 * ============================================================ */

/* SV: import "DPI-C" function int c_add(input int a, input int b); */
int c_add(int a, int b)
{
    printf("[C][c_add]  %d + %d = %d\n", a, b, a + b);
    return a + b;
}

/* SV: import "DPI-C" function real c_multiply_real(input real x, input real y); */
double c_multiply_real(double x, double y)
{
    printf("[C][c_multiply_real]  %.4f * %.4f = %.4f\n", x, y, x * y);
    return x * y;
}

/* SV: import "DPI-C" function void c_print_string(input string msg);
 *
 * 重要：SV string 傳到 C 是 const char*
 *   - 不能呼叫 free()
 *   - 不能修改內容
 *   - 指標只在這次函式呼叫期間有效，不要把它存起來
 */
void c_print_string(const char* msg)
{
    printf("[C][c_print_string]  \"%s\"  (len=%zu)\n", msg, strlen(msg));
}

/* SV: import "DPI-C" function int c_string_length(input string s); */
int c_string_length(const char* s)
{
    return (int)strlen(s);
}

/* SV: import "DPI-C" function bit c_check_even(input int n);
 *
 * svBit = unsigned char，只能是 0 或 1
 * 對應 SV 的 bit 型別（1-bit 2-state logic）
 */
svBit c_check_even(int n)
{
    printf("[C][c_check_even]  %d 是%s數\n", n, (n % 2 == 0) ? "偶" : "奇");
    return (svBit)(n % 2 == 0 ? 1 : 0);
}

/* SV: import "DPI-C" function byte c_to_upper(input byte ch);
 *
 * SV byte = 8-bit 有號整數（-128 ~ 127）
 * Xcelium svdpi.h 裡沒有 svByte，直接用 signed char
 * 兩者的 ABI（記憶體布局、呼叫慣例）完全相同
 */
signed char c_to_upper(signed char ch)
{
    signed char result = (signed char)toupper((unsigned char)ch);
    printf("[C][c_to_upper]  '%c' -> '%c'\n", ch, result);
    return result;
}


/* ============================================================
 *  [區塊 2] Open Array 操作
 *
 *  當 SV 傳陣列給 C，C 端收到 svOpenArrayHandle
 *  這是一個不透明的 handle，必須透過以下 API 存取：
 *
 *  維度查詢（dim 從 1 開始，不是 0）：
 *    svLeft (h, dim)  → 左邊界 index（不一定是 0！）
 *    svRight(h, dim)  → 右邊界 index
 *    svSize (h, dim)  → 元素個數 = |right - left| + 1
 *    svDimensions(h)  → 幾維陣列
 *
 *  元素存取（回傳 void*，需自行 cast）：
 *    svGetArrElemPtr1(h, i)     → 一維陣列第 i 個元素
 *    svGetArrElemPtr2(h, i, j)  → 二維陣列第 [i][j] 元素
 *    svGetArrElemPtr3(h,i,j,k)  → 三維陣列
 *
 *  注意：
 *    - index 必須用 svLeft..svRight 的範圍，不能假設從 0 開始
 *    - SV 宣告 int arr[1:8] 的 left=1, right=8
 *    - SV 宣告 int arr[8]   的 left=0, right=7（packed shorthand）
 *    - inout 方向才能修改元素；input 方向也能修改指標內容，
 *      但這是 undefined behavior，不要這樣做
 * ============================================================ */

/* SV: import "DPI-C" function void c_fill_array(inout int arr[]); */
void c_fill_array(svOpenArrayHandle arr)
{
    int left  = svLeft (arr, 1);   /* 最小 index（可能不是 0） */
    int right = svRight(arr, 1);   /* 最大 index */
    int size  = svSize (arr, 1);   /* 元素個數 */

    printf("[C][c_fill_array]  index [%d:%d], 共 %d 個元素\n", left, right, size);

    for (int i = left; i <= right; i++) {
        int* elem = (int*)svGetArrElemPtr1(arr, i);
        if (elem) *elem = i * i;   /* 填入 index 的平方 */
    }
    printf("[C][c_fill_array]  填入 arr[i]=i^2 完成\n");
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

    /* 先把資料複製出來，再反序寫回 */
    int* buf = (int*)malloc(size * sizeof(int));
    for (int i = left; i <= right; i++) {
        int* e = (int*)svGetArrElemPtr1(arr, i);
        buf[i - left] = e ? *e : 0;
    }
    for (int i = left; i <= right; i++) {
        int* e = (int*)svGetArrElemPtr1(arr, i);
        if (e) *e = buf[right - i];   /* right - i 做反序映射 */
    }
    free(buf);
    printf("[C][c_reverse_array]  反序完成\n");
}

/* SV: import "DPI-C" function void c_print_2d_array(input int arr[][]); 
 *
 * 二維 open array：
 *   dim=1 → 第一維（row）
 *   dim=2 → 第二維（col）
 * svGetArrElemPtr2(arr, row, col) 存取特定元素
 */
void c_print_2d_array(svOpenArrayHandle arr)
{
    int r_left  = svLeft (arr, 1);
    int r_right = svRight(arr, 1);
    int c_left  = svLeft (arr, 2);
    int c_right = svRight(arr, 2);

    printf("[C][c_print_2d_array]  row[%d:%d] col[%d:%d]\n",
           r_left, r_right, c_left, c_right);

    for (int r = r_left; r <= r_right; r++) {
        printf("  row[%d]: ", r);
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
 *  SV 端：
 *    typedef struct { int id; int value; real score; } SVPacket;
 *    import "DPI-C" function void c_process_packet(input SVPacket pkt);
 *
 *  C 端：
 *    typedef struct { int id; int value; double score; ... } CPacket;
 *
 *  注意事項：
 *    1. 欄位順序必須兩端完全一致
 *    2. SV real = C double（64-bit），對應要正確
 *    3. SV string 不能放在 struct 裡傳給 C
 *       → 改用 byte array（char[]）代替
 *    4. padding：C 編譯器可能會在欄位間插入 padding bytes
 *       → 如有問題可加 __attribute__((packed)) 強制不 padding
 *    5. input → C 端收到 const 指標（不能修改）
 *       inout → C 端收到一般指標（可以讀寫）
 * ============================================================ */

/* SV: import "DPI-C" function void c_process_packet(input SVPacket pkt); */
void c_process_packet(const CPacket* pkt)
{
    printf("[C][c_process_packet]  id=%d value=%d score=%.2f name=\"%s\"\n",
           pkt->id, pkt->value, pkt->score, pkt->name);
}

/* SV: import "DPI-C" function void c_fill_packet(inout SVPacket pkt, ...); */
void c_fill_packet(CPacket* pkt, int id, double score)
{
    /* inout → C 端可以修改 struct 的欄位，修改會反映回 SV */
    pkt->id    = id;
    pkt->value = id * 10;
    pkt->score = score;
    snprintf(pkt->name, sizeof(pkt->name), "packet_%03d", id);
    printf("[C][c_fill_packet]  id=%d score=%.2f\n", id, score);
}


/* ============================================================
 *  [區塊 4] Blocking Task
 *
 *  SV 端用 task 宣告（不是 function）：
 *    import "DPI-C" context task c_blocking_sort(inout int arr[]);
 *
 *  C 端規則：
 *    - 函式必須回傳 int
 *    - 回傳 0 = 正常結束（對應 SV task return）
 *    - 回傳 1 = disable（相當於 SV 的 disable <task_name>）
 *    - 回傳其他值 → 模擬器報錯（就是之前的 INVDIS 錯誤）
 *
 *  context 屬性：
 *    加了 context 才能在 C 端呼叫 svGetScope() 等 API
 *    blocking task 通常都需要加 context
 * ============================================================ */

/* SV: import "DPI-C" context task c_blocking_sort(inout int arr[]); */
int c_blocking_sort(svOpenArrayHandle arr)
{
    int left  = svLeft (arr, 1);
    int right = svRight(arr, 1);
    int size  = svSize (arr, 1);
    printf("[C][c_blocking_sort]  排序 %d 個元素...\n", size);

    /* 把資料取出做 bubble sort，再寫回 */
    int* buf = (int*)malloc(size * sizeof(int));
    for (int i = left; i <= right; i++) {
        int* e = (int*)svGetArrElemPtr1(arr, i);
        buf[i - left] = e ? *e : 0;
    }
    /* Bubble sort */
    for (int i = 0; i < size - 1; i++)
        for (int j = 0; j < size - i - 1; j++)
            if (buf[j] > buf[j+1]) {
                int t = buf[j]; buf[j] = buf[j+1]; buf[j+1] = t;
            }
    /* 寫回（inout → 改動反映回 SV） */
    for (int i = left; i <= right; i++) {
        int* e = (int*)svGetArrElemPtr1(arr, i);
        if (e) *e = buf[i - left];
    }
    free(buf);
    printf("[C][c_blocking_sort]  排序完成\n");
    return 0;  /* 0 = 正常結束；1 = disable */
}


/* ============================================================
 *  [區塊 5] Chandle — C 物件指標管理
 *
 *  SV 的 chandle 型別 ↔ C 的 void*
 *
 *  使用情境：
 *    - C 端有複雜的物件（struct / class），想讓 SV 保存它的指標
 *    - SV 不知道指標指向什麼，只是存放並在需要時傳回 C 端
 *    - C 端透過 create / use / destroy 管理物件生命週期
 *
 *  重要：
 *    - 記憶體由 C 端負責管理（malloc / free）
 *    - SV 的 GC 不管 chandle 指向的記憶體
 *    - 必須在不需要時主動 destroy，否則 memory leak
 *    - SV 端可以把 chandle 存在變數、struct、動態陣列裡
 *    - chandle = null 代表空指標
 * ============================================================ */

/* 這是 C 端的私有結構，SV 端完全不知道它的內容 */
typedef struct {
    int  count;
    char name[16];
} Counter;

/* SV: import "DPI-C" function chandle c_create_counter(input int init_val);
 * 回傳 void* → SV 端存成 chandle
 */
void* c_create_counter(int init_val)
{
    Counter* c = (Counter*)malloc(sizeof(Counter));
    c->count = init_val;
    snprintf(c->name, sizeof(c->name), "CTR_%d", init_val);
    printf("[C][c_create_counter]  \"%s\" init=%d addr=%p\n",
           c->name, c->count, (void*)c);
    return (void*)c;   /* void* → SV 的 chandle */
}

/* SV: import "DPI-C" function void c_increment(input chandle handle);
 * SV 傳入 chandle → C 收到 void*，自行 cast 成正確型別
 */
void c_increment(void* handle)
{
    if (!handle) { fprintf(stderr, "[C] c_increment: null handle!\n"); return; }
    Counter* c = (Counter*)handle;   /* cast 回正確型別 */
    c->count++;
    printf("[C][c_increment]  \"%s\" count=%d\n", c->name, c->count);
}

/* SV: import "DPI-C" function int c_get_count(input chandle handle); */
int c_get_count(void* handle)
{
    if (!handle) return -1;
    return ((Counter*)handle)->count;
}

/* SV: import "DPI-C" function void c_destroy_counter(input chandle handle);
 * 呼叫後 SV 端應把變數設成 null：counter_handle = null;
 */
void c_destroy_counter(void* handle)
{
    if (!handle) return;
    Counter* c = (Counter*)handle;
    printf("[C][c_destroy_counter]  釋放 \"%s\" addr=%p\n", c->name, handle);
    free(c);   /* 釋放記憶體，SV 端的 chandle 此後不能再使用 */
}


/* ============================================================
 *  [區塊 6] svdpi.h 進階 API
 *
 *  這些 API 只能在 "context" function/task 裡呼叫
 *  （非 context 的一般 function 呼叫會回傳 NULL 或失敗）
 *
 *  Xcelium 23.x 實際可用的 API：
 *
 *  Scope 相關：
 *    svScope svGetScope()
 *      → 取得「目前正在執行的 SV scope」
 *      → 只有 context function/task 才能呼叫
 *      → 可以存起來，之後用 svSetScope() 切換回去
 *
 *    svScope svSetScope(svScope s)
 *      → 切換到指定 scope
 *      → 回傳切換前的 scope（可用來還原）
 *      → 在多 instance 設計中，讓 C 端知道要操作哪個 instance
 *
 *    const char* svGetNameFromScope(svScope s)
 *      → 取得 scope 的名稱字串（如 "tb_top" 或 "tb_top.dut"）
 *
 *  UserData 相關（在 scope 上綁定任意 C 資料）：
 *    int svPutUserData(svScope s, void* key, void* data)
 *      → 把 data 綁定到 scope s 上，用 key 識別
 *      → key 通常用靜態變數的地址（保證唯一）
 *
 *    void* svGetUserData(svScope s, void* key)
 *      → 取回之前存入的 data
 *      → 找不到 key 時回傳 NULL
 *
 *  UserData 使用情境：
 *    C 端可以在 scope 上存放任何資料（如 counter、state machine）
 *    每次被 SV 呼叫時取回，實現「跨呼叫的 C 端狀態」
 *
 *  時間相關（Xcelium 23.x）：
 *    svGetSimTime() / svGetSimNtime() 在這個版本的 svdpi.h 不存在
 *    最可靠的做法是從 SV 端把 $time 當參數傳進來：
 *      import "DPI-C" function void c_log(input longint t, input string msg);
 *      → 呼叫：c_log($time, "something happened");
 * ============================================================ */

/* SV: import "DPI-C" context function void c_use_scope_api(); */
void c_use_scope_api(void)
{
    /*
     * svGetScope() 回傳「是誰呼叫這個函式的 SV scope」
     * 只有 context function 才能呼叫，否則回傳 NULL
     */
    svScope scope = svGetScope();

    if (!scope) {
        printf("[C][c_use_scope_api]  scope=NULL (需要 context function)\n");
        return;
    }

    /* svGetNameFromScope：把 scope 轉成可讀的名稱字串 */
    const char* name = svGetNameFromScope(scope);
    printf("[C][c_use_scope_api]  目前 scope = \"%s\"\n",
           name ? name : "(unknown)");

    /*
     * 進階用法：存下 scope，之後可以 svSetScope(saved) 切換回來
     * 在多 instance 設計中非常有用：
     *
     *   svScope saved = svGetScope();
     *   svSetScope(other_scope);
     *   sv_some_export_func();   // 在 other_scope 裡執行
     *   svSetScope(saved);       // 還原
     */
}

/* SV: import "DPI-C" context function void c_use_time_api(); */
void c_use_time_api(void)
{
    /*
     * 取得模擬時間的推薦做法：
     *
     * 在 SV 端把 $time 當參數傳進來最可靠，例如：
     *   import "DPI-C" function void c_print_time(input longint t);
     *   → 呼叫：c_print_time($time);
     *
     * 這樣 C 端直接收到一個 long long，不需要依賴
     * 任何 svdpi.h 裡可能因版本不同而不存在的 API
     *
     * 如果你的 svdpi.h 有 svGetSimTime()，可以這樣用：
     *   uint64_t ticks = svGetSimTime();   // 以 timeprecision 為單位
     *   double   ntime = svGetSimNtime();  // normalized 時間
     */
    printf("[C][c_use_time_api]  時間 API 已呼叫\n");
    printf("[C]  推薦做法：從 SV 端把 $time 當參數傳進來\n");
    printf("[C]  例：import \"DPI-C\" function void c_log_time(input longint t);\n");
}

/* SV: import "DPI-C" context function void c_use_userdata(); */
void c_use_userdata(void)
{
    /*
     * svPutUserData / svGetUserData 使用模式：
     *
     * 1. 定義一個靜態變數作為 key（地址保證唯一）
     * 2. 第一次呼叫：malloc 資料，用 svPutUserData 綁定到 scope
     * 3. 之後的呼叫：用 svGetUserData 取回資料，讀取或修改
     *
     * 效果：C 端在不同呼叫之間可以保存狀態，
     *        而且每個 SV scope instance 有自己獨立的資料
     */
    static int key;          /* 靜態變數地址 = 唯一的 key */
    svScope    scope = svGetScope();

    if (!scope) {
        printf("[C][c_use_userdata]  scope=NULL\n");
        return;
    }

    int* data = (int*)svGetUserData(scope, &key);

    if (!data) {
        /* 第一次呼叫：建立資料並綁定到 scope */
        data  = (int*)malloc(sizeof(int));
        *data = 1000;
        svPutUserData(scope, &key, data);
        printf("[C][c_use_userdata]  第一次：建立 userdata=%d\n", *data);
    } else {
        /* 後續呼叫：取回資料並修改 */
        (*data)++;
        printf("[C][c_use_userdata]  後續呼叫：userdata=%d\n", *data);
    }
}


/* ============================================================
 *  [區塊 7] Pure 函式
 *
 *  SV 端宣告：import "DPI-C" pure function int c_pure_fibonacci(input int n);
 *
 *  pure 的意義：
 *    相同輸入 → 永遠相同輸出，無任何副作用
 *
 *  模擬器因此可以：
 *    - 快取結果：相同參數不重複呼叫 C
 *    - 平行執行：多個 pure 函式同時呼叫沒有 race condition
 *
 *  pure 函式的限制（違反這些 = undefined behavior）：
 *    ✗ 不能呼叫任何 svdpi.h API（svGetScope 等）
 *    ✗ 不能有任何 I/O（printf、file 等）
 *    ✗ 不能讀寫 static / global 變數
 *    ✗ 不能有任何 side-effect
 *
 *  注意：這裡的實作為了示意加了 printf 的位置，
 *        實際 pure 函式請完全拿掉 I/O
 * ============================================================ */

/* SV: import "DPI-C" pure function int c_pure_fibonacci(input int n); */
int c_pure_fibonacci(int n)
{
    if (n <= 0) return 0;
    if (n == 1) return 1;
    /* 迭代計算，避免遞迴的指數複雜度 */
    int a = 0, b = 1;
    for (int i = 2; i <= n; i++) {
        int t = a + b;
        a = b;
        b = t;
    }
    return b;
}

/* SV: import "DPI-C" pure function real c_pure_power(input real base, input int exp); */
double c_pure_power(double base, int exp)
{
    double r = 1.0;
    for (int i = 0; i < exp; i++) r *= base;
    return r;
}


/* ============================================================
 *  [Export 回呼示範]
 *
 *  SV 端定義了 export function：
 *    export "DPI-C" function sv_compute_crc;
 *
 *  C 端要呼叫它，需要：
 *  1. 有函式原型（用 extern 宣告，或從 -dpiimpheader 生成的 header include）
 *  2. import 這個 C 函式的 SV 端要宣告成 "context"：
 *       import "DPI-C" context function void c_call_sv_export(...);
 *     → 少了 context 會報 NONCONI 錯誤
 *
 *  C 呼叫 SV export 的限制：
 *    - 只能在 context function/task 的呼叫鏈中使用
 *    - 不能在 thread / callback / signal handler 裡呼叫
 *    - 呼叫當下 SV 端是「暫停的」，相當於 SV 把控制權交給 C
 * ============================================================ */

/*
 * sv_compute_crc 是 SV 端 export 的函式
 * 原型由模擬器在 -dpiimpheader 產生的 header 裡宣告
 * 這裡用 extern 手動宣告以便 C 端呼叫
 */
extern int sv_compute_crc(int data);

/* SV: import "DPI-C" context function void c_call_sv_export(input int input_data); */
void c_call_sv_export(int input_data)
{
    printf("[C][c_call_sv_export]  呼叫 sv_compute_crc(0x%08X)\n", input_data);

    /*
     * 這裡 C 端主動呼叫 SV 定義的函式
     * 這就是 DPI 的雙向呼叫：SV→C→SV
     * 必須確保呼叫鏈上所有 import 都有 context 屬性
     */
    int crc = sv_compute_crc(input_data);
    printf("[C][c_call_sv_export]  SV 回傳 CRC=0x%08X\n", crc);
}
