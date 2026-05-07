# SystemVerilog DPI 完整學習筆記

## 專案結構

```
sv_dpi_project/
├── sv/
│   └── tb_top.sv          ← SV testbench（所有 DPI 宣告 + 測試）
├── c/
│   ├── dpi_functions.h    ← C 端 header（含 svdpi.h API 完整說明）
│   └── dpi_functions.c    ← C 端實作（所有 DPI 功能 + 教學註解）
└── scripts/
    ├── run_xrun.sh        ← 執行腳本
    └── xrun.f             ← xrun filelist
```

---

## 快速執行

```bash
# 進入專案根目錄（sv/ 和 c/ 都在這層）
cd sv_dpi_project

# 方法 1：執行腳本（推薦）
chmod +x scripts/run_xrun.sh
./scripts/run_xrun.sh

# 方法 2：用 filelist
xrun -f scripts/xrun.f

# 方法 3：一行指令（最精簡）
xrun -sv sv/tb_top.sv c/dpi_functions.c \
     -dpiimpheader dpi_imports.h \
     -CFLAGS "-I${CDSHOME}/tools/include -g" \
     -access +r -log xrun.log -mess -top tb_top

# 清除編譯結果
./scripts/run_xrun.sh -clean
```

---

## DPI 功能速查表

### 1. 基本型別對應（Xcelium 23.x）

| SV 型別    | C 型別        | 說明                                       |
|-----------|--------------|-------------------------------------------|
| `int`     | `int`         | 32-bit 有號整數                            |
| `real`    | `double`      | 64-bit 浮點數                              |
| `string`  | `const char*` | 唯讀！不能 `free()`，不能修改內容            |
| `bit`     | `svBit`       | `= unsigned char`，值只有 0 或 1           |
| `byte`    | `signed char` | ⚠️ `svByte` 在 Xcelium 23.x 不存在！       |
| `shortint`| `short`       | 16-bit 整數                                |
| `longint` | `long long`   | 64-bit 整數                                |
| `chandle` | `void*`       | 不透明指標，SV 保存、C 端 malloc/free 管理  |
| `void`    | `void`        | 無回傳值                                   |

### 2. 宣告語法與 context 說明

```systemverilog
// === SV → C (import) ===

// 一般函式：C 只做純計算，不呼叫任何 svdpi API
import "DPI-C" function int c_add(input int a, input int b);

// context 函式：C 內部需要呼叫 svGetScope() / svPutUserData()
//               或需要回呼 SV 的 export function
// 少了 context 且呼叫 export → 報 NONCONI 錯誤
// 少了 context 且呼叫 svGetScope() → 回傳 NULL
import "DPI-C" context function void c_use_scope();
import "DPI-C" context function void c_call_sv_export(input int d);

// pure 函式：相同輸入永遠相同輸出，無任何副作用
//            模擬器可快取結果或平行執行
//            不能有 I/O、不能用 static 變數、不能呼叫 svdpi API
import "DPI-C" pure function int c_fibonacci(input int n);

// import task：C 端耗時任務，一定要加 context
//              C 函式回傳 int：0=正常結束，1=disable
//              回傳其他值 → 報 INVDIS 錯誤
import "DPI-C" context task c_blocking_op(inout int arr[]);

// === C → SV (export) ===
export "DPI-C" function sv_my_func;

function int sv_my_func(input int x);
    return x * 2;
endfunction
```

### 3. context 屬性三種比較

| 屬性        | 可呼叫 svdpi API | 可回呼 export | 可有 I/O | 可用 static | 模擬器最佳化 |
|------------|----------------|--------------|---------|------------|------------|
| `(無)`      | ✗              | ✗            | ✓       | ✓          | 無          |
| `context`  | ✓              | ✓            | ✓       | ✓          | 無          |
| `pure`     | ✗              | ✗            | ✗       | ✗          | 可快取/平行 |

### 4. Open Array 傳遞

```systemverilog
// SV 端
int arr[8];          // index 0..7
int arr2[1:8];       // index 1..8（自訂 range！不一定從 0 開始）
import "DPI-C" function void c_process(inout int arr[]);
```

```c
// C 端
void c_process(svOpenArrayHandle arr) {
    int left  = svLeft (arr, 1);   // 左邊界（可能不是 0！）
    int right = svRight(arr, 1);   // 右邊界
    int size  = svSize (arr, 1);   // 元素個數

    for (int i = left; i <= right; i++) {
        int* elem = (int*)svGetArrElemPtr1(arr, i);
        *elem = i;  // inout → 修改會反映回 SV
    }
}

// 二維陣列用 svGetArrElemPtr2(arr, row, col)
// dim 參數從 1 開始（不是 0）
```

> **svLeft / svRight / svGetArrElemPtr 從哪裡來？**
> 這些是 IEEE 1800 SystemVerilog 標準（Annex H）定義的 API，
> 存在於 `$CDSHOME/tools/include/svdpi.h`，`#include "svdpi.h"` 即可使用。
> 詳細清單見 `dpi_functions.h` 最上方的說明區塊。

### 5. Chandle（C 物件指標）

```systemverilog
// SV 端
chandle my_obj;
import "DPI-C" function chandle c_create(input int init);
import "DPI-C" function void    c_use   (input chandle h);
import "DPI-C" function void    c_destroy(input chandle h);

initial begin
    my_obj = c_create(10);   // C malloc → 回傳 void* → SV 存成 chandle
    c_use(my_obj);
    c_destroy(my_obj);       // C free（SV 的 GC 不管 chandle 指向的記憶體！）
    my_obj = null;           // 清空 SV 端的 handle
end
```

```c
// C 端
typedef struct { int count; char name[16]; } Counter;

void* c_create(int init) {
    Counter* c = malloc(sizeof(Counter));
    c->count = init;
    return (void*)c;        // void* → SV 的 chandle
}
void c_use(void* h) {
    Counter* c = (Counter*)h;  // cast 回正確型別
    c->count++;
}
void c_destroy(void* h) {
    free(h);                // 必須手動釋放！
}
```

### 6. Blocking Task 的 C 端回傳值

```c
// import task 對應的 C 函式必須回傳 int（不是 void！）
int c_blocking_sort(svOpenArrayHandle arr) {
    // ... 做耗時操作 ...
    return 0;   // 0 = 正常結束
                // 1 = disable（相當於 SV 的 disable <task>）
                // 其他值 → xmsim 報 INVDIS 錯誤
}
```

### 7. xrun 旗標速查（Xcelium 23.x 實測）

| 旗標                      | 說明                                         |
|--------------------------|---------------------------------------------|
| `-sv`                    | 啟用 SystemVerilog                           |
| `file.c`                 | 直接把 C 檔放進去一起編譯                     |
| `-sv_lib mylib.so`       | 載入預先編譯好的 shared library               |
| `-dpiimpheader out.h`    | 產生 C 端用的 header（含 SV export 函式原型）  |
| `-CFLAGS "..."`          | 傳給 C 編譯器的旗標                          |
| `-ldargs "..."`          | ⚠️ 傳給 linker 的旗標（不是 `-LDFLAGS`！）    |
| `-access +r`             | 允許讀取 signal（debug 用）                   |
| `-database waves.shm`    | ⚠️ 儲存波形（不是 `-shm`，23.x 已移除）       |
| `-gui`                   | 開啟 SimVision GUI                           |
| `-mess`                  | 顯示詳細訊息                                 |
| `-top <module>`          | 指定 top module                              |

### 8. 常見錯誤與解法（實際踩過的坑）

| 錯誤訊息 | 原因 | 解法 |
|---------|------|------|
| `*E,BDOPT: Unknown option -LDFLAGS` | xrun 無此旗標 | 改用 `-ldargs "-lm"` |
| `*E,BDOPT: Unknown option -shm` | 23.x 已移除 | 改用 `-database waves.shm` |
| `*F,WRKBAD: logical library name WORK is bound to a bad library` | `-work` 帶絕對路徑，xrun 會拼接到 `xcelium.d/` | 移除 `-work`，讓 xrun 用預設 |
| `error: unknown type name 'svByte'` | Xcelium svdpi.h 無此型別 | 改用 `signed char` |
| `*E,NONCONI: cannot be executed from a non-context` | C 函式回呼了 SV export，但 import 沒加 `context` | 加 `context`：`import "DPI-C" context function ...` |
| `*F,INVDIS: import task returned a value other than 1 or 0` | import task 對應的 C 函式宣告為 `void` | 改成回傳 `int`，`return 0;` |
| `svGetScope() 回傳 NULL` | import 沒加 `context` | 加 `context` |

---

## 實際執行輸出（參考）

```
╔══════════════════════════════════════════════════════╗
║      SystemVerilog DPI 完整學習範例  by xrun         ║
╚══════════════════════════════════════════════════════╝

── [Test 1] 基本型別傳遞 ─────────────────────────────
[C][c_add]  100 + 234 = 334
[SV] c_add 回傳: 334
[C][c_multiply_real]  3.1400 * 2.7100 = 8.5094
[C][c_to_upper]  'a' -> 'A'

── [Test 2] Open Array ───────────────────────────────
[C][c_fill_array]  index [0:7], 共 8 個元素
[SV] arr1 = 0 1 4 9 16 25 36 49
[C][c_sum_array]   總和 = 140
[C][c_reverse_array]  反序完成
[C][c_print_2d_array]  row[0:3] col[0:3]

── [Test 3] Struct 傳遞 ──────────────────────────────
[C][c_process_packet]  id=42 value=1000 score=98.75
[C][c_fill_packet]  id=99 score=77.50

── [Test 4] Export Function (C 呼叫 SV) ─────────────
[SV][sv_compute_crc]  data=0xdeadbeef  CRC=0x43
[C][c_call_sv_export]  呼叫 sv_compute_crc(0xCAFE1234)
[SV][sv_compute_crc]  data=0xcafe1234  CRC=0xad

── [Test 5] Blocking Task ────────────────────────────
[SV] 排序前: 5 3 8 1 9 2 7 4 6 0
[C][c_blocking_sort]  排序完成
[SV] 排序後: 0 1 2 3 4 5 6 7 8 9

── [Test 6] Chandle (C 物件指標) ────────────────────
[C][c_create_counter]  "CTR_10" init=10
[C][c_increment]  "CTR_10" count=15
[SV] c_get_count 回傳: 15 (應為 15)
[C][c_destroy_counter]  釋放 "CTR_10"

── [Test 7] svdpi.h 進階 API ─────────────────────────
[C][c_use_scope_api]  目前 scope = "$unit_0x4bff31f0::"
[C][c_use_userdata]  第一次：建立 userdata=1000
[C][c_use_userdata]  後續呼叫：userdata=1001
[C][c_use_userdata]  後續呼叫：userdata=1002

── [Test 8] Pure Function ────────────────────────────
fib(0)=0 fib(1)=1 ... fib(10)=55
[SV] 2^10 = 1024.000000
[SV] 3^ 5 = 243.000000

╔══════════════════════════════════════════════════════╗
║               所有 DPI 測試完成！                    ║
╚══════════════════════════════════════════════════════╝
Simulation complete via $finish(1) at time 70 NS + 0
```

## xrun.log

```
============================================================
  SystemVerilog DPI 完整學習範例 — xrun
  Project root : /home/users3/kenny780/kenny/DPI/sv_dpi_project
============================================================

TOOL:   xrun    23.03-s013: Started on May 08, 2026 at 04:30:55 CST
xrun: 23.03-s013: (c) Copyright 1995-2024 Cadence Design Systems, Inc.
Recompiling... reason: file './sv/tb_top.sv' is newer than expected.
        expected: Thu May  7 23:02:51 2026
        actual:   Fri May  8 04:30:47 2026
file: sv/tb_top.sv
        module worklib.tb_top:sv
                errors: 0, warnings: 0
        Elaborating the design hierarchy:
        Top level design units:
                $unit_0x4bff31f0
                tb_top
        Building instance overlay tables: .................... Done
        Generating native compiled code:
                worklib.tb_top:sv <0x6cbc1945>
                        streams:   1, words: 43789
        Building instance specific data structures.
        Loading native compiled code:     .................... Done
        Design hierarchy summary:
                                 Instances  Unique
                Modules:                 1       1
                Registers:              60      30
                Initial blocks:          1       1
                Compilation units:       1       1
                Simulation timescale:  1ps
        Writing initial simulation snapshot: worklib.tb_top:sv
Loading snapshot worklib.tb_top:sv .................... Done
xcelium> source /home/project/eda/pkgs/cadence/xcelium/v23.03/tools/xcelium/files/xmsimrc
xcelium> run


╔══════════════════════════════════════════════════════╗
║      SystemVerilog DPI 完整學習範例  by xrun          ║
╚══════════════════════════════════════════════════════╝

── [Test 1] 基本型別傳遞 ─────────────────────────────
[C][c_add]  100 + 234 = 334
[SV] c_add 回傳: 334
[C][c_multiply_real]  3.1400 * 2.7100 = 8.5094
[SV] c_multiply_real 回傳: 8.509400
[C][c_print_string]  "Hello from SV!"  (len=14)
[SV] c_string_length("systemverilog") = 13
[C][c_check_even]  42 是偶數
[SV] c_check_even(42) = 1  (應為 1)
[C][c_check_even]  7 是奇數
[SV] c_check_even( 7) = 0  (應為 0)
[C][c_to_upper]  'a' -> 'A'
[SV] c_to_upper('a') = 'A' (0x41)

── [Test 2] Open Array ───────────────────────────────
[SV] 呼叫 c_fill_array(arr1[0:7])...
[C][c_fill_array]  index [0:7], 共 8 個元素
[C][c_fill_array]  填入 arr[i]=i^2 完成
[SV] arr1 = 0 1 4 9 16 25 36 49
[C][c_sum_array]   總和 = 140
[SV] c_sum_array 回傳總和: 140
[SV] arr2 反序前 = 3 6 9 12 15 18 21 24
[C][c_reverse_array]  反序完成
[SV] arr2 反序後 = 24 21 18 15 12 9 6 3
[SV] 二維陣列初始值：
  row[0]:   0   1   2   3
  row[1]:  10  11  12  13
  row[2]:  20  21  22  23
  row[3]:  30  31  32  33
[SV] 呼叫 c_print_2d_array...
[C][c_print_2d_array]  row[0:3] col[0:3]
  row[0]:    0    1    2    3
  row[1]:   10   11   12   13
  row[2]:   20   21   22   23
  row[3]:   30   31   32   33

── [Test 3] Struct 傳遞 ──────────────────────────────
[SV] 傳遞 struct 給 C：id=42 value=1000 score=98.750000
[C][c_process_packet]  id=42 value=1000 score=98.75 name=""
[C][c_fill_packet]  id=99 score=77.50
[SV] C 填充後：id=99 value=990 score=77.500000

── [Test 4] Export Function (C 呼叫 SV) ─────────────
[SV][sv_compute_crc]  data=0xdeadbeef  CRC=0x43
[SV] sv_compute_crc(0xDEADBEEF) = 0x43
[SV] 呼叫 c_call_sv_export → C 內部再呼叫 sv_compute_crc
[C][c_call_sv_export]  呼叫 sv_compute_crc(0xCAFE1234)
[SV][sv_compute_crc]  data=0xcafe1234  CRC=0xad
[C][c_call_sv_export]  SV 回傳 CRC=0x000000AD

── [Test 5] Blocking Task ────────────────────────────
[SV] 排序前: 5 3 8 1 9 2 7 4 6 0
[SV] 呼叫 c_blocking_sort (task)...
[C][c_blocking_sort]  排序 10 個元素...
[C][c_blocking_sort]  排序完成
[SV] 排序後: 0 1 2 3 4 5 6 7 8 9

── [Test 6] Chandle (C 物件指標) ────────────────────
[C][c_create_counter]  "CTR_10" init=10 addr=0xccc6640
[SV] counter_handle = 214722112
[C][c_increment]  "CTR_10" count=11
[C][c_increment]  "CTR_10" count=12
[C][c_increment]  "CTR_10" count=13
[C][c_increment]  "CTR_10" count=14
[C][c_increment]  "CTR_10" count=15
[SV] c_get_count 回傳: 15 (應為 15)
[C][c_destroy_counter]  釋放 "CTR_10" addr=0xccc6640

── [Test 7] svdpi.h 進階 API ─────────────────────────
[SV] 呼叫 c_use_scope_api...
[C][c_use_scope_api]  目前 scope = "$unit_0x4bff31f0::"
[SV] 呼叫 c_use_time_api (時間=20000)...
[C][c_use_time_api]  時間 API 已呼叫
[C]  推薦做法：從 SV 端把 $time 當參數傳進來
[C]  例：import "DPI-C" function void c_log_time(input longint t);
[SV] 呼叫 c_use_userdata 三次...
[C][c_use_userdata]  第一次：建立 userdata=1000
[C][c_use_userdata]  後續呼叫：userdata=1001
[C][c_use_userdata]  後續呼叫：userdata=1002

── [Test 8] Pure Function ────────────────────────────
fib(0)=0 fib(1)=1 fib(2)=1 fib(3)=2 fib(4)=3 fib(5)=5 fib(6)=8 fib(7)=13 fib(8)=21 fib(9)=34 fib(10)=55
[SV] 2^10 = 1024.000000 (應為 1024)
[SV] 3^ 5 = 243.000000 (應為  243)


╔══════════════════════════════════════════════════════╗
║               所有 DPI 測試完成！                     ║
╚══════════════════════════════════════════════════════╝

Simulation complete via $finish(1) at time 70 NS + 0
./sv/tb_top.sv:381         $finish;
xcelium> exit
TOOL:   xrun    23.03-s013: Exiting on May 08, 2026 at 04:30:56 CST  (total: 00:00:01)

==> 完成！Log 檔案：xrun.log
```
