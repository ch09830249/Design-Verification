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
