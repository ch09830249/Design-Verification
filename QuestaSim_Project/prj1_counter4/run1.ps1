# 產生亂數種子（用時間）
$seed = Get-Date -Format "HHmmssff"
Write-Host "Using seed: $seed"

# 確保 log1 資料夾存在
New-Item -ItemType Directory -Path "./log1" -Force | Out-Null

# 指定工作庫資料夾為 ./log1/work
vlib ./log1/work

# 編譯設計（DUT）：counter4.sv
vlog -work ./log1/work ./rtl/counter4.sv

# 編譯測試平台（TB）：tb_top.sv，並加入 ./tb 為 include 路徑。 
vlog -work ./log1/work +incdir+./tb ./tb/tb_top.sv

# 執行模擬，指定：
# - 指定亂數種子
# - 指定工作庫位置
# - 指定 wlf 波形輸出檔
# - 將 transcript 檔案寫到 ./log1/transcript
& vsim -sv_seed $seed -lib ./log1/work tb_top `
      -wlf ./log1/wave.wlf `
      -do "view wave; add wave -recursive sim:/tb_top; run -all" `	# 1. 自動開啟波形視窗 2. 將波形加到視窗中 3.執行模擬直到結束
      > ./log1/transcript 2>&1
	 