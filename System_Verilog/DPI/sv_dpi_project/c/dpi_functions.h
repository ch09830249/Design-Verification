#ifndef DPI_FUNCTIONS_H
#define DPI_FUNCTIONS_H

/*
 * ============================================================
 *  DPI 完整學習專案 — C 端 Header
 *  涵蓋所有 DPI 功能類別
 * ============================================================
 *
 *  功能分類：
 *  1. 基本型別傳遞   (int / real / string / bit)
 *  2. 陣列操作       (open array / packed array)
 *  3. Export 回呼    (C 呼叫 SV 定義的函式)
 *  4. Blocking task  (C 端耗時任務)
 *  5. Chandle        (C 物件指標傳遞)
 *  6. svdpi.h API    (scope / time / userdata)
 *  7. Pure 函式      (無 side-effect，模擬器可最佳化)
 * ============================================================
 */

#include "svdpi.h"  /* SystemVerilog DPI 標準 header */
#include <stdint.h>

/* ----------------------------------------------------------
 *  SV export 宣告 — 這些是在 SV 端定義、C 端呼叫的函式
 *  (由模擬器自動產生，這裡只是示意，實際不需要手動宣告)
 * ---------------------------------------------------------- */
/* extern int  sv_compute_crc(int data); */
/* extern void sv_notify_done(const char* msg); */

/* ----------------------------------------------------------
 *  1. 基本型別
 * ---------------------------------------------------------- */
extern int    c_add(int a, int b);
extern double c_multiply_real(double x, double y);
extern void   c_print_string(const char* msg);
extern int    c_string_length(const char* s);
extern svBit  c_check_even(int n);          /* 回傳 SV bit 型別 */
extern svByte c_to_upper(svByte ch);        /* svByte = signed char */

/* ----------------------------------------------------------
 *  2. Open Array (動態大小陣列)
 * ---------------------------------------------------------- */
extern void c_fill_array    (svOpenArrayHandle arr);
extern int  c_sum_array     (svOpenArrayHandle arr);
extern void c_reverse_array (svOpenArrayHandle arr);
extern void c_print_2d_array(svOpenArrayHandle arr);  /* 二維陣列 */

/* ----------------------------------------------------------
 *  3. Struct / Packed 資料
 * ---------------------------------------------------------- */
typedef struct {
    int   id;
    int   value;
    double score;
    char  name[32];
} CPacket;

extern void c_process_packet(const CPacket* pkt);
extern void c_fill_packet   (CPacket* pkt, int id, double score);

/* ----------------------------------------------------------
 *  4. Blocking task (耗時任務，SV 端宣告為 task)
 * ---------------------------------------------------------- */
extern void c_blocking_sort(svOpenArrayHandle arr);   /* 模擬耗時排序 */

/* ----------------------------------------------------------
 *  5. Chandle — C 物件指標
 * ---------------------------------------------------------- */
extern void*  c_create_counter (int init_val);   /* 回傳 chandle */
extern void   c_increment      (void* handle);
extern int    c_get_count      (void* handle);
extern void   c_destroy_counter(void* handle);

/* ----------------------------------------------------------
 *  6. svdpi.h API 進階操作
 * ---------------------------------------------------------- */
extern void c_use_scope_api  (void);  /* 使用 svGetScope / svSetScope */
extern void c_use_time_api   (void);  /* 使用 svGetTime            */
extern void c_use_userdata   (void);  /* 使用 svPutUserData / svGetUserData */

/* ----------------------------------------------------------
 *  7. Pure 函式 (context-free，無 side-effect)
 *     在 SV 端用 "DPI-C" pure 宣告
 * ---------------------------------------------------------- */
extern int    c_pure_fibonacci(int n);   /* 純計算，無任何 SV/IO 互動 */
extern double c_pure_power    (double base, int exp);

#endif /* DPI_FUNCTIONS_H */
