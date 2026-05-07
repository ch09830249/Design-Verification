// ============================================================
//  DPI 完整學習專案 — SystemVerilog 端 Testbench
//  tb_top.sv
//
//  涵蓋所有 DPI 功能：
//  1. 基本型別傳遞   (int / real / string / bit / byte)
//  2. Open Array     (動態陣列，一維 & 二維)
//  3. Struct         (傳遞結構體)
//  4. Export function (SV 定義，C 端呼叫)
//  5. Blocking task  (C 端耗時任務)
//  6. Chandle        (C 物件指標)
//  7. svdpi.h API    (scope / time / userdata)
//  8. Pure function  (無 side-effect)
// ============================================================
`timescale 1ns/1ps

// ------------------------------------------------------------
//  [1] 基本型別 — import 宣告
//
//  格式：import "DPI-C" [pure|context] function|task <sv_type> <fname>(...);
//
//  型別對應：
//    SV int     <-> C int
//    SV real    <-> C double
//    SV string  <-> C const char*
//    SV bit     <-> C svBit
//    SV byte    <-> C signed char  (Xcelium svdpi.h 無 svByte)
//    SV chandle <-> C void*
// ------------------------------------------------------------
import "DPI-C" function int    c_add           (input int a, input int b);
import "DPI-C" function real   c_multiply_real (input real x, input real y);
import "DPI-C" function void   c_print_string  (input string msg);
import "DPI-C" function int    c_string_length  (input string s);
import "DPI-C" function bit    c_check_even     (input int n);
import "DPI-C" function byte   c_to_upper       (input byte ch);  // C端: signed char

// ------------------------------------------------------------
//  [2] Open Array — 動態大小陣列
//
//  SV 端宣告時用 [] 表示 open array dimension
//  C 端收到 svOpenArrayHandle，透過 API 存取元素
//
//  input  → C 端只讀
//  inout  → C 端可讀寫 (改動會反映回 SV)
//  output → C 端只寫
// ------------------------------------------------------------
import "DPI-C" function void c_fill_array    (inout  int arr[]);
import "DPI-C" function int  c_sum_array     (input  int arr[]);
import "DPI-C" function void c_reverse_array (inout  int arr[]);
import "DPI-C" function void c_print_2d_array(input  int arr[][]);

// ------------------------------------------------------------
//  [3] Struct — 注意 SV 與 C 的 struct layout 需對齊
//
//  SV 的 packed struct 對應 C 的 struct（需注意 padding）
//  建議：使用 typedef struct，並在兩端保持相同欄位順序
//
//  這裡示範用 input/inout 傳遞 struct
// ------------------------------------------------------------
typedef struct {
    int    id;
    int    value;
    real   score;
    // 注意：SV string 不能放在 struct 裡傳給 C
    // 改用 byte array 代替
} SVPacket;

import "DPI-C" function void c_process_packet(input  SVPacket pkt);
import "DPI-C" function void c_fill_packet   (inout  SVPacket pkt,
                                               input  int     id,
                                               input  real    score);

// ------------------------------------------------------------
//  [4] Export Function — SV 定義，C 端呼叫
//
//  格式：export "DPI-C" function <function_name>;
//  函式本體在 SV 裡定義 (用 function / task 關鍵字)
//  C 端透過函式指標或直接呼叫（需要模擬器生成的 header）
// ------------------------------------------------------------
// SV 端的 export function 宣告
export "DPI-C" function sv_compute_crc;
export "DPI-C" function sv_notify_done;

// 讓 C 呼叫的 export 函式，在 SV 端呼叫 C 函式
// (這個 C 函式會再回呼 sv_compute_crc，展示 cross-call)
import "DPI-C" context function void c_call_sv_export(input int input_data);

// ------------------------------------------------------------
//  [5] Blocking Task — C 端耗時任務
//
//  SV task 可以消耗模擬時間
//  import task 讓 C 端也能有類似的行為
//
//  重要：blocking task 需要 "context" 屬性
//  context = 可以呼叫 svGetScope() 等需要 SV context 的 API
// ------------------------------------------------------------
import "DPI-C" context task c_blocking_sort(inout int arr[]);

// ------------------------------------------------------------
//  [6] Chandle — C 物件指標
//
//  chandle 是 SV 的不透明指標型別
//  SV 不知道它指向什麼，只能存放並傳回 C 端
//  用來實作 C 端的物件導向模式
// ------------------------------------------------------------
import "DPI-C" function chandle c_create_counter (input int init_val);
import "DPI-C" function void    c_increment      (input chandle handle);
import "DPI-C" function int     c_get_count      (input chandle handle);
import "DPI-C" function void    c_destroy_counter(input chandle handle);

// ------------------------------------------------------------
//  [7] svdpi.h 進階 API
//
//  context function = 可以使用 svGetScope() / svGetTime() 等 API
//  一般 function 不能使用這些 API
// ------------------------------------------------------------
import "DPI-C" context function void c_use_scope_api();
import "DPI-C" context function void c_use_time_api ();
import "DPI-C" context function void c_use_userdata ();

// ------------------------------------------------------------
//  [8] Pure Function — 無 side-effect
//
//  pure = 相同輸入永遠相同輸出，無任何副作用
//  模擬器可以：
//    - 快取結果（相同輸入不重複計算）
//    - 平行執行（無 race condition）
//  限制：不能呼叫任何 svdpi.h API、不能有 I/O、不能用 static 變數
// ------------------------------------------------------------
import "DPI-C" pure function int    c_pure_fibonacci(input int    n);
import "DPI-C" pure function real   c_pure_power    (input real   base,
                                                     input int    exp);


// ============================================================
//  Export 函式實作（SV 端）
// ============================================================

// CRC-8 簡單實作（SV 端，供 C 端呼叫）
function int sv_compute_crc(int data);
    automatic int crc = 8'hFF;
    automatic int poly = 8'h31;  // CRC-8/MAXIM polynomial
    for (int i = 7; i >= 0; i--) begin
        automatic bit bit_val = (data >> i) & 1;
        automatic bit top_bit = (crc >> 7) & 1;
        crc = crc << 1;
        if (top_bit ^ bit_val) crc = crc ^ poly;
        crc = crc & 8'hFF;
    end
    $display("[SV][sv_compute_crc]  data=0x%08X  CRC=0x%02X", data, crc);
    return crc;
endfunction

// 完成通知（SV 端，供 C 端呼叫）
function void sv_notify_done(string msg);
    $display("[SV][sv_notify_done]  收到來自 C 的通知: \"%s\"", msg);
endfunction


// ============================================================
//  Testbench 主體
// ============================================================
module tb_top;

    // ---- 測試用變數 ----
    int    result_int;
    real   result_real;
    bit    result_bit;
    byte   result_byte;
    string test_str;
    chandle counter_handle;

    // Open array 測試
    int arr1[8];          // 一維，index 0..7
    int arr2[1:8];        // 一維，index 1..8（自訂 range）
    int arr_2d[0:3][0:3]; // 二維 4x4
    int arr_sort[10];

    // Struct 測試
    SVPacket pkt;

    // ----------------------------------------------------------
    initial begin

        $display("\n");
        $display("╔══════════════════════════════════════════════════════╗");
        $display("║      SystemVerilog DPI 完整學習範例  by xrun         ║");
        $display("╚══════════════════════════════════════════════════════╝");


        // ======================================================
        //  測試 1：基本型別傳遞
        // ======================================================
        $display("\n── [Test 1] 基本型別傳遞 ─────────────────────────────");

        // int
        result_int = c_add(100, 234);
        $display("[SV] c_add 回傳: %0d", result_int);

        // real
        result_real = c_multiply_real(3.14, 2.71);
        $display("[SV] c_multiply_real 回傳: %f", result_real);

        // string
        test_str = "Hello from SV!";
        c_print_string(test_str);
        result_int = c_string_length("systemverilog");
        $display("[SV] c_string_length(\"systemverilog\") = %0d", result_int);

        // bit
        result_bit = c_check_even(42);
        $display("[SV] c_check_even(42) = %b  (應為 1)", result_bit);
        result_bit = c_check_even(7);
        $display("[SV] c_check_even( 7) = %b  (應為 0)", result_bit);

        // byte → char 操作
        result_byte = c_to_upper(byte'("a"));
        $display("[SV] c_to_upper('a') = '%c' (0x%02X)", result_byte, result_byte);


        // ======================================================
        //  測試 2：Open Array
        // ======================================================
        $display("\n── [Test 2] Open Array ───────────────────────────────");

        // 2-1: 讓 C 填充陣列
        $display("[SV] 呼叫 c_fill_array(arr1[0:7])...");
        c_fill_array(arr1);
        $write("[SV] arr1 = ");
        foreach (arr1[i]) $write("%0d ", arr1[i]);
        $display("");

        // 2-2: 求和
        result_int = c_sum_array(arr1);
        $display("[SV] c_sum_array 回傳總和: %0d", result_int);

        // 2-3: 反序（自訂 index range）
        foreach (arr2[i]) arr2[i] = i * 3;
        $write("[SV] arr2 反序前 = ");
        foreach (arr2[i]) $write("%0d ", arr2[i]);
        $display("");
        c_reverse_array(arr2);
        $write("[SV] arr2 反序後 = ");
        foreach (arr2[i]) $write("%0d ", arr2[i]);
        $display("");

        // 2-4: 二維陣列
        foreach (arr_2d[r, c]) arr_2d[r][c] = r * 10 + c;
        $display("[SV] 二維陣列初始值：");
        foreach (arr_2d[r, c]) begin
            if (c == 0) $write("  row[%0d]: ", r);
            $write("%3d ", arr_2d[r][c]);
            if (c == 3) $display("");
        end
        $display("[SV] 呼叫 c_print_2d_array...");
        c_print_2d_array(arr_2d);


        // ======================================================
        //  測試 3：Struct 傳遞
        // ======================================================
        $display("\n── [Test 3] Struct 傳遞 ──────────────────────────────");

        // 3-1: SV 端填好 struct 傳給 C
        pkt.id    = 42;
        pkt.value = 1000;
        pkt.score = 98.75;
        $display("[SV] 傳遞 struct 給 C：id=%0d value=%0d score=%f",
                 pkt.id, pkt.value, pkt.score);
        c_process_packet(pkt);

        // 3-2: 讓 C 端填充 struct (inout)
        c_fill_packet(pkt, 99, 77.5);
        $display("[SV] C 填充後：id=%0d value=%0d score=%f",
                 pkt.id, pkt.value, pkt.score);


        // ======================================================
        //  測試 4：Export Function (C 呼叫 SV)
        // ======================================================
        $display("\n── [Test 4] Export Function (C 呼叫 SV) ─────────────");

        // 直接測試 sv_compute_crc (SV 端自呼)
        result_int = sv_compute_crc(32'hDEAD_BEEF);
        $display("[SV] sv_compute_crc(0xDEADBEEF) = 0x%02X", result_int);

        // 讓 C 端去呼叫 sv_compute_crc（cross-call）
        $display("[SV] 呼叫 c_call_sv_export → C 內部再呼叫 sv_compute_crc");
        c_call_sv_export(32'hCAFE_1234);


        // ======================================================
        //  測試 5：Blocking Task
        // ======================================================
        $display("\n── [Test 5] Blocking Task ────────────────────────────");

        // 初始化亂序陣列
        arr_sort = '{5, 3, 8, 1, 9, 2, 7, 4, 6, 0};
        $write("[SV] 排序前: ");
        foreach (arr_sort[i]) $write("%0d ", arr_sort[i]);
        $display("");

        $display("[SV] 呼叫 c_blocking_sort (task)...");
        #10;  // 加一點時間延遲，示意 task 會消耗模擬時間
        c_blocking_sort(arr_sort);
        #10;

        $write("[SV] 排序後: ");
        foreach (arr_sort[i]) $write("%0d ", arr_sort[i]);
        $display("");


        // ======================================================
        //  測試 6：Chandle (C 物件指標)
        // ======================================================
        $display("\n── [Test 6] Chandle (C 物件指標) ────────────────────");

        // 建立 C 端物件，取得 chandle
        counter_handle = c_create_counter(10);
        $display("[SV] counter_handle = %p", counter_handle);

        // 操作 C 端物件
        repeat(5) c_increment(counter_handle);

        // 讀取 C 端物件狀態
        result_int = c_get_count(counter_handle);
        $display("[SV] c_get_count 回傳: %0d (應為 15)", result_int);

        // 釋放 C 端物件
        c_destroy_counter(counter_handle);
        counter_handle = null;  // 清除 SV 端的 handle


        // ======================================================
        //  測試 7：svdpi.h 進階 API
        // ======================================================
        $display("\n── [Test 7] svdpi.h 進階 API ─────────────────────────");

        $display("[SV] 呼叫 c_use_scope_api...");
        c_use_scope_api();

        $display("[SV] 呼叫 c_use_time_api (時間=%0t)...", $time);
        #50;
        c_use_time_api();

        $display("[SV] 呼叫 c_use_userdata 三次...");
        c_use_userdata();
        c_use_userdata();
        c_use_userdata();


        // ======================================================
        //  測試 8：Pure Function
        // ======================================================
        $display("\n── [Test 8] Pure Function ────────────────────────────");

        // Fibonacci
        for (int n = 0; n <= 10; n++) begin
            result_int = c_pure_fibonacci(n);
            $write("fib(%0d)=%0d ", n, result_int);
        end
        $display("");

        // Power
        result_real = c_pure_power(2.0, 10);
        $display("[SV] 2^10 = %f (應為 1024)", result_real);

        result_real = c_pure_power(3.0, 5);
        $display("[SV] 3^ 5 = %f (應為  243)", result_real);


        // ======================================================
        //  完成
        // ======================================================
        $display("\n");
        $display("╔══════════════════════════════════════════════════════╗");
        $display("║               所有 DPI 測試完成！                    ║");
        $display("╚══════════════════════════════════════════════════════╝");
        $display("");

        $finish;
    end

endmodule
