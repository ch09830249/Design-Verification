# ============================================================
#  xrun.f — xrun filelist / argument file
#  用法：xrun -f xrun.f
# ============================================================

# ---- 基本設定 -----------------------------------------------
-sv
-timescale 1ns/1ps
-access +r
-mess
-log xrun.log
-top tb_top

# ---- SV 檔案 ------------------------------------------------
sv/tb_top.sv

# ---- C 檔案 -------------------------------------------------
c/dpi_functions.c

# ---- DPI Header 輸出 ----------------------------------------
# 在工作目錄產生 C 可用的 header（含 SV export function 原型）
-dpiimpheader work/dpi_imports.h

# ---- 編譯旗標 -----------------------------------------------
# 注意：${CDSHOME} 需要在 shell 環境中設定好
-CFLAGS "-g -I${CDSHOME}/tools/include -Iwork"
-LDFLAGS "-lm"

# ---- Work library -------------------------------------------
-work work/worklib
