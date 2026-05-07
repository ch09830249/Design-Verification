#!/bin/bash
# ============================================================
#  DPI 完整學習專案 — xrun 執行腳本 (修正版 v5)
#  使用方式：
#    cd sv_dpi_project          ← 一定要在專案根目錄執行！
#    chmod +x scripts/run_xrun.sh
#    ./scripts/run_xrun.sh
#    ./scripts/run_xrun.sh -clean
#    ./scripts/run_xrun.sh -wave
# ============================================================

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

CLEAN=0; GUI=0; WAVE=0
for arg in "$@"; do
    case "$arg" in
        -clean) CLEAN=1 ;;
        -gui)   GUI=1   ;;
        -wave)  WAVE=1  ;;
        *) echo "未知參數: $arg"; exit 1 ;;
    esac
done

if [ "$CLEAN" -eq 1 ]; then
    echo "==> 清除..."
    rm -rf xcelium.d xrun.log waves.shm *.err dpi_imports.h
    echo "    清除完成"; exit 0
fi

echo "============================================================"
echo "  SystemVerilog DPI 完整學習範例 — xrun"
echo "  Project root : ${PROJECT_ROOT}"
echo "============================================================"
echo ""

cd "${PROJECT_ROOT}"

EXTRA_FLAGS=""
if [ "$WAVE" -eq 1 ]; then
    EXTRA_FLAGS="-database waves.shm -access +rwc"
fi
if [ "$GUI" -eq 1 ]; then
    EXTRA_FLAGS="${EXTRA_FLAGS} -gui"
fi

# ---- 執行 xrun ----------------------------------------------
# 修正：
#   -ldargs "-lm"  → 移除（xrun 不接受這個格式，且 m32 環境通常不需要）
#   若真的需要連結額外 library，改用 -Wld,<flag> 傳給 linker
xrun \
    -sv \
    sv/tb_top.sv \
    c/dpi_functions.c \
    -dpiimpheader dpi_imports.h \
    -CFLAGS "-I${CDSHOME}/tools/include -g" \
    -timescale 1ns/1ps \
    -access +r \
    -log xrun.log \
    -mess \
    -top tb_top \
    ${EXTRA_FLAGS}

echo ""
echo "==> 完成！Log 檔案：xrun.log"
