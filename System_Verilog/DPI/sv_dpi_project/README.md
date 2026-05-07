# SystemVerilog DPI 完整學習筆記

## 專案結構

```
sv_dpi_project/
├── sv/
│   └── tb_top.sv          ← SV testbench（所有 DPI 宣告 + 測試）
├── c/
│   ├── dpi_functions.h    ← C 端 header
│   └── dpi_functions.c    ← C 端實作（所有 DPI 功能）
└── scripts/
    ├── run_xrun.sh        ← 執行腳本
    └── xrun.f             ← xrun filelist
```

---

## 快速執行

```bash
# 進入專案目錄
cd sv_dpi_project

# 方法 1：直接執行腳本
chmod +x scripts/run_xrun.sh
./scripts/run_xrun.sh

# 方法 2：用 filelist
xrun -f scripts/xrun.f

# 方法 3：一行指令
xrun -sv sv/tb_top.sv c/dpi_functions.c \
     -dpiimpheader work/dpi_imports.h \
     -CFLAGS "-I${CDSHOME}/tools/include -Iwork" \
     -LDFLAGS "-lm" \
     -access +r -log xrun.log
```

---

## DPI 功能速查表

### 1. 基本型別對應

| SV 型別    | C 型別          | 說明                        |
|-----------|-----------------|----------------------------|
| `int`     | `int`           | 32-bit 有號整數             |
| `real`    | `double`        | 64-bit 浮點數               |
| `string`  | `const char*`   | 唯讀！不能 free / 修改      |
| `bit`     | `svBit`         | `unsigned char`，值 0 或 1  |
| `byte`    | `svByte`        | `signed char`               |
| `shortint`| `short`         | 16-bit 整數                 |
| `longint` | `long long`     | 64-bit 整數                 |
| `chandle` | `void*`         | 不透明指標，SV 保存 C 物件   |
| `void`    | `void`          | 無回傳值                    |

### 2. 宣告語法

```systemverilog
// === SV → C (import) ===

// 一般函式（不能用 svdpi API）
import "DPI-C" function int c_add(input int a, input int b);

// Context 函式（可以用 svGetScope / svGetTime 等）
import "DPI-C" context function void c_use_scope();

// Pure 函式（無 side-effect，模擬器可最佳化）
import "DPI-C" pure function int c_fibonacci(input int n);

// Import task（可消耗模擬時間）
import "DPI-C" context task c_blocking_op(inout int arr[]);

// === C → SV (export) ===
export "DPI-C" function sv_my_func;

// SV 端的 function 定義
function int sv_my_func(input int x);
    return x * 2;
endfunction
```

### 3. 陣列傳遞

```systemverilog
// SV 端
int arr[8];
import "DPI-C" function void c_process(inout int arr[]);

// C 端
void c_process(svOpenArrayHandle arr) {
    int left  = svLeft (arr, 1);   // 最小 index
    int right = svRight(arr, 1);   // 最大 index
    int size  = svSize (arr, 1);   // 元素個數

    for (int i = left; i <= right; i++) {
        int* elem = (int*)svGetArrElemPtr1(arr, i);
        *elem = i;  // 修改會反映回 SV
    }
}
```

### 4. Chandle（C 物件）

```systemverilog
// SV 端
chandle my_obj;
import "DPI-C" function chandle c_create();
import "DPI-C" function void    c_use   (chandle h);
import "DPI-C" function void    c_free  (chandle h);

initial begin
    my_obj = c_create();   // 取得 C 物件指標
    c_use(my_obj);         // 操作 C 物件
    c_free(my_obj);        // 釋放（SV 不管理記憶體！）
    my_obj = null;
end
```

```c
// C 端
typedef struct { int x; int y; } Point;

void* c_create() {
    Point* p = malloc(sizeof(Point));
    p->x = 0; p->y = 0;
    return (void*)p;       // 回傳 void* → SV 的 chandle
}

void c_use(void* h) {
    Point* p = (Point*)h;  // 轉回正確型別
    p->x++;
}

void c_free(void* h) {
    free(h);               // 手動釋放！
}
```

### 5. xrun 重要旗標

| 旗標                        | 說明                                    |
|----------------------------|----------------------------------------|
| `-sv`                      | 啟用 SystemVerilog                      |
| `file.c`                   | 直接把 C 檔放進去一起編譯                |
| `-sv_lib mylib.so`         | 載入預先編譯好的 shared library         |
| `-dpiimpheader out.h`      | 產生 C 端用的 header（含 export 原型）   |
| `-CFLAGS "..."`            | 傳給 C 編譯器的旗標                     |
| `-LDFLAGS "..."`           | 傳給 linker 的旗標                      |
| `-access +r`               | 允許讀取 signal（debug 用）              |
| `-shm`                     | 儲存波形（.shm 格式）                   |
| `-gui`                     | 開啟 SimVision GUI                     |
| `-mess`                    | 顯示詳細訊息                            |

### 6. 常見錯誤與解法

**找不到 svdpi.h**
```bash
find $CDSHOME -name "svdpi.h"
# 通常在 $CDSHOME/tools/include/svdpi.h
# 加入：-CFLAGS "-I${CDSHOME}/tools/include"
```

**C 函式找不到（link error）**
- 確認 C 函式名稱與 SV 的 `import "DPI-C"` 宣告完全一致
- 確認 C 函式沒有 C++ name mangling（C++ 需要 `extern "C"`）

**svGetScope() 回傳 NULL**
- 確認 SV 端宣告是 `context function` 或 `context task`
- 一般 function 無法呼叫 svGetScope

**陣列 index out of range**
- 用 `svLeft(arr, 1)` 和 `svRight(arr, 1)` 取得正確邊界
- 不要假設 index 從 0 開始！SV 陣列可以是任意 range

### 7. Pure vs Context vs 一般

| 屬性      | 可用 svdpi API | 可有 I/O | 可用 static | 模擬器最佳化 |
|----------|---------------|---------|------------|------------|
| 一般      | ✗             | ✓       | ✓          | 無          |
| `context` | ✓             | ✓       | ✓          | 無          |
| `pure`    | ✗             | ✗       | ✗          | 可快取/平行 |

---

## 預期輸出

```
╔══════════════════════════════════════════════════════╗
║      SystemVerilog DPI 完整學習範例  by xrun         ║
╚══════════════════════════════════════════════════════╝

── [Test 1] 基本型別傳遞 ─────────────────────────────
[C][c_add]  100 + 234 = 334
[SV] c_add 回傳: 334
...

── [Test 2] Open Array ───────────────────────────────
[C][c_fill_array]  index [0:7], 共 8 個元素
[SV] arr1 = 0 1 4 9 16 25 36 49
...

── [Test 6] Chandle (C 物件指標) ────────────────────
[C][c_create_counter]  建立計數器 "CTR_10" 初始值=10
[C][c_increment]  "CTR_10" count = 11
...
[SV] c_get_count 回傳: 15 (應為 15)
[C][c_destroy_counter]  釋放計數器...
...

╔══════════════════════════════════════════════════════╗
║               所有 DPI 測試完成！                    ║
╚══════════════════════════════════════════════════════╝
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
