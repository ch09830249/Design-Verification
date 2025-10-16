# 產生亂數種子（用時間）
$seed = Get-Date -Format "HHmmssff"
Write-Host "Using seed: $seed"

# 確保 log 資料夾存在
New-Item -ItemType Directory -Path "./log" -Force | Out-Null

# 指定工作庫資料夾為 ./log/work
vlib ./log/work

# 編譯 DUT
vlog -work ./log/work ./rtl/counter4.sv

# 編譯 TB，加上 incdir
vlog -work ./log/work +incdir+./tb ./tb/tb_top.sv

# 執行模擬，指定：
# - 指定亂數種子
# - 指定工作庫位置
# - 指定 wlf 波形輸出檔
# - 將 transcript 檔案寫到 ./log/transcript
& vsim -sv_seed $seed -lib ./log/work tb_top `
      -wlf ./log/wave.wlf `
      -do "log -r /*; run -all" `
      > ./log/transcript 2>&1