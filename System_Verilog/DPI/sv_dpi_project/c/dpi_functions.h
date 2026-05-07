#ifndef DPI_FUNCTIONS_H
#define DPI_FUNCTIONS_H

/*
 * ============================================================
 *  DPI 完整學習專案 — C 端 Header (Final)
 *  dpi_functions.h
 *
 *  這個 header 宣告所有供 SV 端 import 的 C 函式
 *
 *  包含規則：
 *    - 必須 include "svdpi.h"（Xcelium 提供的標準 DPI header）
 *    - svdpi.h 定義了 svBit、svOpenArrayHandle、svScope 等型別
 *    - svdpi.h 路徑：$CDSHOME/tools/include/svdpi.h
 *      編譯時加 -CFLAGS "-I${CDSHOME}/tools/include"
 *
 *  Xcelium 23.x svdpi.h 存在的型別：
 *    svBit             unsigned char（值 0 或 1）
 *    svOpenArrayHandle 動態陣列 handle
 *    svScope           SV scope 物件
 *    svBitVecVal       packed bit vector
 *    svLogicVecVal     packed logic vector（含 X/Z）
 *
 *  Xcelium 23.x svdpi.h 不存在的型別（常見誤用）：
 *    svByte            → 改用 signed char
 *    svTimeVal         → 改用「SV 傳 $time 進來」的模式
 * ============================================================
 */

#include "svdpi.h"   /* Xcelium DPI 標準 header，定義 svBit 等型別 */
#include <stdint.h>

/* ----------------------------------------------------------
 *  [1] 基本型別函式
 *
 *  SV 型別   → C 型別
 *  int       → int
 *  real      → double
 *  string    → const char*（唯讀！）
 *  bit       → svBit (= unsigned char)
 *  byte      → signed char（svdpi.h 無 svByte）
 * ---------------------------------------------------------- */
extern int          c_add           (int a, int b);
extern double       c_multiply_real (double x, double y);
extern void         c_print_string  (const char* msg);
extern int          c_string_length (const char* s);
extern svBit        c_check_even    (int n);
extern signed char  c_to_upper      (signed char ch);   /* SV byte <-> C signed char */

/* ----------------------------------------------------------
 *  [2] Open Array
 *
 *  SV 宣告 int arr[]  → C 端收到 svOpenArrayHandle
 *  透過 svLeft/svRight/svSize/svGetArrElemPtr1 操作
 *
 *  inout → C 端修改會反映回 SV
 *  input → 只讀（不應修改）
 * ---------------------------------------------------------- */
extern void c_fill_array    (svOpenArrayHandle arr);   /* inout */
extern int  c_sum_array     (svOpenArrayHandle arr);   /* input */
extern void c_reverse_array (svOpenArrayHandle arr);   /* inout */
extern void c_print_2d_array(svOpenArrayHandle arr);   /* input，二維 */

/* ----------------------------------------------------------
 *  [3] Struct 傳遞
 *
 *  SV struct 欄位順序和 C struct 必須完全一致
 *  SV real → C double
 *  SV string 不能在 struct 裡，改用 char[]
 * ---------------------------------------------------------- */
typedef struct {
    int    id;
    int    value;
    double score;
    char   name[32];
} CPacket;

extern void c_process_packet(const CPacket* pkt);   /* input → const */
extern void c_fill_packet   (CPacket* pkt, int id, double score); /* inout → 可修改 */

/* ----------------------------------------------------------
 *  [4] Blocking Task
 *
 *  SV 端：import "DPI-C" context task c_blocking_sort(...);
 *  C 端：回傳 int（不是 void！）
 *    return 0 = 正常結束
 *    return 1 = disable（相當於 SV 的 disable <task>）
 *  回傳其他值 → xmsim 報 INVDIS 錯誤
 * ---------------------------------------------------------- */
extern int  c_blocking_sort(svOpenArrayHandle arr);

/* ----------------------------------------------------------
 *  [5] Chandle — C 物件指標
 *
 *  SV chandle <-> C void*
 *  C 端負責 malloc/free，SV 端只是存放 handle
 *  SV 端設 null 表示清空：counter_handle = null;
 * ---------------------------------------------------------- */
extern void*  c_create_counter (int init_val);   /* 回傳 void* → SV chandle */
extern void   c_increment      (void* handle);
extern int    c_get_count      (void* handle);
extern void   c_destroy_counter(void* handle);   /* 必須手動呼叫，否則 memory leak */

/* ----------------------------------------------------------
 *  [6] svdpi.h 進階 API（需要 context function）
 *
 *  SV 端宣告必須加 context：
 *    import "DPI-C" context function void c_use_scope_api();
 *  否則 svGetScope() 會回傳 NULL
 * ---------------------------------------------------------- */
extern void c_use_scope_api(void);   /* 示範 svGetScope / svGetNameFromScope */
extern void c_use_time_api (void);   /* 示範取時間的推薦做法 */
extern void c_use_userdata (void);   /* 示範 svPutUserData / svGetUserData */

/* ----------------------------------------------------------
 *  [7] Pure 函式（無 side-effect）
 *
 *  SV 端：import "DPI-C" pure function int c_pure_fibonacci(input int n);
 *  pure 函式不能：呼叫 svdpi API、有 I/O、用 static/global 變數
 *  模擬器可以快取結果或平行執行
 * ---------------------------------------------------------- */
extern int    c_pure_fibonacci(int n);
extern double c_pure_power    (double base, int exp);

/* ----------------------------------------------------------
 *  [Export 回呼]
 *
 *  C 端呼叫 SV 定義的 export function
 *  SV 端的 import 宣告必須加 context：
 *    import "DPI-C" context function void c_call_sv_export(input int d);
 *  否則報 NONCONI 錯誤
 * ---------------------------------------------------------- */
extern void c_call_sv_export(int input_data);

#endif /* DPI_FUNCTIONS_H */
