/*
    SystemVerilog 的 DPI（Direct Programming Interface） 是一個強大的工具，可以讓你在 SystemVerilog 和 C/C++ 之間互相呼叫函式，
    常用在模擬、驗證、模型整合等情境。

    DPI（Direct Programming Interface） 是 SystemVerilog 跟 C 語言溝通的橋樑：
        你可以從 SystemVerilog 去呼叫 C/C++ 的函數（稱為 DPI-C）。
        也可以讓 C/C++ 反過來呼叫 SystemVerilog（較少用，稱為 DPI-SV）。
*/

// 基本用法流程（DPI-C）
// 1️⃣ 在 SystemVerilog 中宣告 C 函式：

import "DPI-C" function int my_add(int a, int b);

// 這句話的意思是：「我要匯入一個 C 寫的函式 my_add()，它會傳回一個整數。」

// 2️⃣ 在 C/C++ 中實作該函式：

// mydpi.c
#include <stdio.h>

int my_add(int a, int b) {
    printf("C: my_add called with %d + %d\n", a, b);
    return a + b;
}

// 3️⃣ 在你的 SystemVerilog 測試平台中呼叫：

module top;

  initial begin
    int result;
    result = my_add(10, 20);
    $display("SV: Result = %0d", result);
  end

endmodule

// 4️⃣ 編譯（以 VCS 為例）：

vcs -sverilog top.sv mydpi.c

/*
    如果你用其他 simulator，例如：

    ModelSim/Questa：需要用 vlog +acc 和 vsim -sv_lib

    Xcelium：xrun 自動支援 DPI
*/

/*
    Methods implemented in SystemVerilog can be called in other foreign languages and need to be specified in an export declaration.
*/
export "DPI-C" function int randomize(int range_a, range_b);