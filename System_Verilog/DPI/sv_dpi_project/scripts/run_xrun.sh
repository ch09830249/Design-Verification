#!/bin/bash
# ============================================================
#  DPI 完整學習專案 — xrun 執行腳本
#  run_xrun.sh
#
#  使用方式：
#    chmod +x run_xrun.sh
#    ./run_xrun.sh
#
#  或傳參數：
#    ./run_xrun.sh -clean      清除之前的編譯結果
#    ./run_xrun.sh -gui        開啟 SimVision GUI
#    ./run_xrun.sh -wave       儲存波形 (.shm)
# ============================================================

set -e   # 任何錯誤就停止

# ---- 路徑設定 -----------------------------------------------
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SV_DIR="${SCRIPT_DIR}/sv"
C_DIR="${SCRIPT_DIR}/c"
WORK_DIR="${SCRIPT_DIR}/work"

# ---- 參數解析 -----------------------------------------------
CLEAN=0
GUI=0
WAVE=0

for arg in "$@"; do
    case "$arg" in
        -clean) CLEAN=1 ;;
        -gui)   GUI=1   ;;
        -wave)  WAVE=1  ;;
        *)      echo "未知參數: $arg" ; exit 1 ;;
    esac
done

# ---- 清除 ---------------------------------------------------
if [ "$CLEAN" -eq 1 ]; then
    echo "==> 清除舊的編譯結果..."
    rm -rf "${WORK_DIR}" xrun.log xcelium.d *.shm *.err
    echo "    清除完成"
    exit 0
fi

mkdir -p "${WORK_DIR}"

echo "============================================================"
echo "  SystemVerilog DPI 完整學習範例 — xrun"
echo "============================================================"

# ---- 組合 xrun 指令 -----------------------------------------
XRUN_CMD="xrun"

# [必要] 啟用 SystemVerilog
XRUN_CMD+=" -sv"

# [SV 檔案]
XRUN_CMD+=" ${SV_DIR}/tb_top.sv"

# [C 檔案] — 直接一起編譯
XRUN_CMD+=" ${C_DIR}/dpi_functions.c"

# [DPI Header 產生]
# -dpiimpheader：產生給 C 端使用的 import function header
#                 (包含 SV export 函式的 C 原型宣告)
# -dpiobjheader：產生 DPI object 的 header (進階用途)
XRUN_CMD+=" -dpiimpheader ${WORK_DIR}/dpi_imports.h"

# [CFLAGS] — 傳給 C 編譯器的旗標
# -I$(CDSHOME)/tools/include  加入 svdpi.h 的搜尋路徑
# -I${WORK_DIR}               加入 dpi_imports.h 的搜尋路徑
XRUN_CMD+=" -CFLAGS \"-I\${CDSHOME}/tools/include -I${WORK_DIR} -g\""

# [Linker flags] — 連結 math library (C 端用了 math.h)
XRUN_CMD+=" -LDFLAGS \"-lm\""

# [Timescale]
XRUN_CMD+=" -timescale 1ns/1ps"

# [Access] — 允許讀取所有 signal（debug / 波形用）
XRUN_CMD+=" -access +r"

# [Log]
XRUN_CMD+=" -log xrun.log"

# [Message 格式] — 顯示更詳細的訊息
XRUN_CMD+=" -mess"

# [Top module]
XRUN_CMD+=" -top tb_top"

# [Work directory]
XRUN_CMD+=" -work ${WORK_DIR}/worklib"

# [波形] (可選)
if [ "$WAVE" -eq 1 ]; then
    echo "==> 啟用波形儲存..."
    XRUN_CMD+=" -shm"
    XRUN_CMD+=" -define DUMP_WAVE"
fi

# [GUI] (可選)
if [ "$GUI" -eq 1 ]; then
    echo "==> 啟用 SimVision GUI..."
    XRUN_CMD+=" -gui"
fi

# ---- 顯示完整指令 -------------------------------------------
echo ""
echo "==> 執行指令："
echo "    ${XRUN_CMD}"
echo ""

# ---- 執行 --------------------------------------------------
eval "${XRUN_CMD}"

echo ""
echo "==> 完成！Log 檔案：xrun.log"
