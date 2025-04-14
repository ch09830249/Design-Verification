/*
always 基本介紹
類型	                用途	                  特性
always	        一般用途（不推薦）	    無明確語意，容易錯誤
always_ff	    時脈同步（flip-flop邏輯）	綜合成 DFF，強烈建議
always_comb	        組合邏輯	           自動感知敏感清單
always_latch	  latch 邏輯（不太建議）	  自動推斷 latch
*/

// 1️⃣ always_ff：時序邏輯（最推薦）=> 用來建構 D flip-flop（暫存器）
always_ff @(posedge clk or negedge rst_n) begin
  if (!rst_n)
    q <= 0;
  else
    q <= d;
end

/*
特點：
  只能用在時序電路
  檢查語意正確性，保護你不小心寫出錯的東西
  可加 reset / enable 等邏輯
*/


// 2️⃣ always_comb：組合邏輯（Combinational）=> 自動推斷敏感清單的 always @(*) 替代
always_comb begin
  y = (sel) ? a : b;
end

/*
特點：
  不會忘記敏感清單（比 always @(*) 更安全）
  模擬器和綜合工具知道你在寫純粹組合邏輯
  不允許重複賦值同一變數，避免 glitch
*/

// 3️⃣ always_latch：電平觸發 latch（極少用）=> 實際上通常是錯誤造成的結果，用這可以「明確表示」你要 latch
always_latch begin
  if (en)
    q = d;
end

/*
特點：
  推斷 latch，適用於有條件賦值但沒給預設值的情況
  較容易產生難除錯的邏輯錯誤
  不推薦使用除非你真的要 latch
*/

// 4️⃣ always（傳統 Verilog 的寫法）
always @(posedge clk) begin
  q <= d;
end

/*
特點：
  SystemVerilog 還支援，但已被 always_ff / always_comb 取代
  沒有語意檢查，容易寫錯、容易誤綜合為 latch
*/

/*
類型	          建議使用	      適合邏輯	      檢查語意	      自動敏感清單	      易寫錯
always_ff	    ✅ 強烈建議	    時序邏輯	        ✅	          ❌（明確指定）	      ❌
always_comb	    ✅ 建議	      組合邏輯	        ✅	              ✅	             ❌
always_latch	 🚫 不建議	      latch	          ✅	              ✅	              ⚠️
always	        ❌ 請避免	     任意	            ❌	              ❌	          ✅（危險）
*/