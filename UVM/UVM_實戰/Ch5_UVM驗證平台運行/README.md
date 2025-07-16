# Phase 機制
## task phase 與 function phase
* phase 依照其是否消耗模擬時間（$time列印出的時間）的特性，可以分成兩大類
  * **function phase**，如 build_phase、connect_phase 等，這些 phase 都不耗費模擬時間，透過**函數**來實現
  * **task phase**，如run_phase等，它們耗費仿真時間，透過**任務**來實現
給 DUT 施加激勵、監測 DUT 的輸出都是在這些 phase 中完成的。灰色背景所示的是 task phase，其他為 function phase
所有的 phase 都會依照圖中的順序**自上而下自動執行**
<img width="1214" height="641" alt="image" src="https://github.com/user-attachments/assets/a957c581-bb00-45c3-8a78-632dd28e4c94" />

## 動態運行 phase
* UVM 引進這 12 個小的 phase 是為了實現更精細的控制
* reset、configure、main、shutdown 四個 phase 是核心
  * **reset_phase** 對 DUT 進行重設、初始化等操作
  * **configure_phase** 則進行 DUT 的配置
  * **main_phase** 則是 DUT 的主要運行的地方
  * **shutdown_phase** 則是做一些與 DUT 斷電相關的操作
## phase 執行順序
* 對 UVM 樹來說，共有三種順序可以選擇，一是**自上而下**，**二是自下而上**，**三是隨機序**
  * **自上而下**
    * 如果在 agent 的 build_phase 之前執行 diver 的 build_phase，此時 driver 還根本沒有實例化，所以呼叫 driver.build_phase只會引發錯誤
      * 在其他 phase 實例化一個 uvm_component，那麼系統會報錯
      * uvm_object 的實例化，則可以在任何 phase 完成
  * **由下而上**
    * 除了 build_phase 之外，所有不耗費仿真時間的 phase（即function phase）都是由下而上執行的
      * 如對於 connect_phase 即先執行 driver 和 monitor 的 connect_phase，再執行 agent 的 connect_phase
  * **按照字典序**
    * 對於同一層次的、具有兄弟關係的 component，如 driver 與 monitor，它們的執行順序是按照字典序的。這裡的字典序的排序
依據new時指定的名字。
      * 假如 monitor 在 new 時指定的名字為 aaa，而 driver 的名字為 bbb，那麼將會先執行 monitor 的 build_phase
```
class my_env extends uvm_env;
  A A_inst0;
  A A_inst1;
  A A_inst2;
  A A_inst3;
  …

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    A_inst0 = A::type_id::create("dddd", this);
    A_inst1 = A::type_id::create("zzzz", this);
    A_inst2 = A::type_id::create("jjjj", this);
    A_inst3 = A::type_id::create("aaaa", this);
  endfunction

  `uvm_component_utils(my_env)

endclass
```
```
class A extends uvm_component;
  …
endclass

function void A::build_phase(uvm_phase phase);
  super.build_phase(phase);
  `uvm_info("A", "build_phase", UVM_LOW)
endfunction

function void A::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  `uvm_info("A", "connect_phase", UVM_LOW)
endfunction
```
```
# UVM_INFO A.sv(16) @ 0: uvm_test_top.env.aaaa [A] build_phase
# UVM_INFO A.sv(16) @ 0: uvm_test_top.env.dddd [A] build_phase
# UVM_INFO A.sv(16) @ 0: uvm_test_top.env.jjjj [A] build_phase
# UVM_INFO A.sv(16) @ 0: uvm_test_top.env.zzzz [A] build_phase
# UVM_INFO A.sv(21) @ 0: uvm_test_top.env.aaaa [A] connect_phase
# UVM_INFO A.sv(21) @ 0: uvm_test_top.env.dddd [A] connect_phase
# UVM_INFO A.sv(21) @ 0: uvm_test_top.env.jjjj [A] connect_phase
# UVM_INFO A.sv(21) @ 0: uvm_test_top.env.zzzz [A] connect_phase
```
* 類似 run_phase、main_phase 等 task_phase 也都是依照**由下而上**的順序執行的。但與前面 function phase 自下而上執行不同的是，這種 task phase 是耗費時間的，所以它並不是等到「下面」的 phase（如 driver 的 run_phase）執行完才執行「上面」的 phase（如 agent 的 run_phase），而是將這些 run_phase 透過 fork…join_none 的形式全部啟動。所以，更準確的說法是**由下而上的啟動，同時在運行**。
* 對於同一 component 來說，其 12 個 run-time 的 phase 是順序執行的，但是它們也只是順序執行，並不是說前面一個 phase 執行完就立即執行後一個 phase。以 main_phase 和 post_main_phase 為例，對於 A component 來說，其 main_phase 在 0 時刻開始執行，100 時刻執行完畢：
* A component
```
task A::main_phase(uvm_phase phase);
  phase.raise_objection(this);
  `uvm_info("A", "main phase start", UVM_LOW)
  #100;
  `uvm_info("A", "main phase end", UVM_LOW)
  phase.drop_objection(this);
endtask

task A::post_main_phase(uvm_phase phase);
  phase.raise_objection(this);
  `uvm_info("A", "post main phase start", UVM_LOW)
  #300;
  `uvm_info("A", "post main phase end", UVM_LOW)
  phase.drop_objection(this);
endtask
```
* B component
```
task B::main_phase(uvm_phase phase);
  phase.raise_objection(this);
  `uvm_info("B", "main phase start", UVM_LOW)
  #200;
  `uvm_info("B", "main phase end", UVM_LOW)
  phase.drop_objection(this);
endtask

task B::post_main_phase(uvm_phase phase);
  phase.raise_objection(this);
  `uvm_info("B", "post main phase start", UVM_LOW)
  #200;
  `uvm_info("B", "post main phase end", UVM_LOW)
  phase.drop_objection(this);
endtask
```
此時整個驗證平台的 main_phase 才執行完畢，接下來執行 post_main_phase，即 A 和 B 的 post_main_phase 都是在 200 時刻開始執行。假設 A 的 post_main_phase 執行完畢需要 300 個時間單位，而 B 只需要 200 個時間單位，無論是 A 或 B，其後續都沒有其他耗時間的 phase 了，整個驗證平台會在 500 時刻關閉。上述程式碼的執行結果如下：
```
# UVM_INFO B.sv(15) @ 0: uvm_test_top.env.B_inst [B] main phase start
# UVM_INFO A.sv(21) @ 0: uvm_test_top.env.A_inst [A] main phase start
# UVM_INFO A.sv(23) @ 100: uvm_test_top.env.A_inst [A] main phase end
# UVM_INFO B.sv(17) @ 200: uvm_test_top.env.B_inst [B] main phase end
# UVM_INFO B.sv(23) @ 200: uvm_test_top.env.B_inst [B] post main phase start
# UVM_INFO A.sv(29) @ 200: uvm_test_top.env.A_inst [A] post main phase start
# UVM_INFO B.sv(25) @ 400: uvm_test_top.env.B_inst [B] post main phase end
# UVM_INFO A.sv(31) @ 500: uvm_test_top.env.A_inst [A] post main phase end
```
可以看到對 A 來說，main_phase 在 100 時刻結束，其 post_main_phase 在 200 時刻開始執行。在 100～200 時刻，A 處於等待 B 的狀態，除了等待不做任何事。 B 的 post_main_phase 在 400 時刻結束，之後就處於等待 A 的狀態。
<img width="1159" height="687" alt="image" src="https://github.com/user-attachments/assets/90b8684d-9a62-4e4a-b0aa-a9f72c85226c" />

## UVM 樹的遍歷
除了兄弟關係的 component，還有一種叔侄關係的 component，如 my_scoreboard 與 my_driver，從樹的層次結構上來說，scoreboard 等級是高於driver 的，但是，這兩者 build_phase 的執行順序其實也是不確定的
* **廣度優先**
  * 指的是如果 i_agt 的 build_phase 執行完畢後，接下來執行的是其兄弟 component 的 build_phase，當所有兄弟的 build_phase 執行完畢後，再執行其孩子的 build_phase
* **深度優先**
  * 指的是如果 i_agt 的 build_phase 執行完畢後，它接下來執行的是其孩子的 build_phase，如果孩子還有孩子，那麼再繼續執行下去，一直到整棵以 i_agt 為樹根的 UVM 子樹的 build_phase 執行完畢，之後再執行 i_agt 的兄弟的 build_phase
* UVM 中採用的是**深度優先的原則**，scoreboard 及 driver 的 build_phase 的執行順序，i_agt 實例化時名字為 “i_agt”，而 scb 為 “scb”，那麼 i_agt 的 build_phase 先執行，在執行完畢後，接下來執行 driver、monitor 及 sequencer 的 build_phase。當全部執行完
畢後再執行 scoreboard 的 build_phase
```
# UVM_INFO my_agent.sv(29) @ 0: uvm_test_top.env.i_agt [agent] build_phase
# UVM_INFO my_driver.sv(16) @ 0: uvm_test_top.env.i_agt.drv [driver] build_phase
# UVM_INFO my_agent.sv(29) @ 0: uvm_test_top.env.o_agt [agent] build_phase
# UVM_INFO my_scoreboard.sv(23) @ 0: uvm_test_top.env.scb [scb] build_phase
```
反之，如果 i_agt 實例化時是 bbb，而 scb 為 aaa，則會先執行 scb 的 build_phase，再執行 i_agt 的 build_phase，接下來是 driver、
monitor 及 sequencer 的 build_phase
## super.phase 的內容
* 對 build_phase 來說，uvm_component 對其做的最重要的事情就是之前所示的自動取得透過 config_db：：set 設定的參數。如果要關掉這個功能，可以在自己的 build_phase 中不呼叫 super.build_phase
* 除了 build_phase 外，UVM 在其他 phase 中幾乎沒有做任何相關的事情
  * 除 build_phase 外，寫其他 phase 時，完全可以不必加上 super.xxxx_phase 語句 (這個結論只適用於直接擴展自 uvm_component 的類別)
## build 階段出現 UVM_ERROR 停止仿真
如果使用 config_db：：get 無法得到 virtual interface，就會直接呼叫 uvm_fatal 結束模擬。由於 virtual interface 對於一個 driver 來說是必須的，所以這種 uvm_fatal 直接退出的使用方式是非常常見的。但是，事實上，如果這裡使用 uvm_error，也會退出：
```
virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if(!uvm_config_db#(virtual my_if)::get(this, "", "vif", vif))
       `uvm_fatal("my_driver", "virtual interface must be set for vif!!!")
    `uvm_error("my_driver", "UVM_ERROR test")
endfunction
```
```
# UVM_ERROR my_driver.sv(16) @ 0: uvm_test_top.env.i_agt.drv [my_driver] UVM_ERROR test
# UVM_FATAL @ 0: reporter [BUILDERR] stopping due to build errors
```
這裡給的 uvm_fatal 是 UVM 內部自訂的。**在 end_of_elaboration_phase 及其前面的 phase 中，如果出現了一個或多個 UVM_ERROR，那麼 UVM 就認為出現了致命錯誤，會呼叫 uvm_fatal 結束模擬**
UVM 的這個特性在小型設計中體現不出優勢，但是在大型設計中，這項特性非常有用。大型設計中，真正模擬前的編譯、優化可能會花費一個多小時的時間。完成編譯、最佳化後開始仿真，幾秒鐘後，出現一個 uvm_fatal 就停止仿真。當修復了這個問題後，再次重新運行，發現又有一個 uvm_fatal 出現。如此反覆，可能會耗費大量時間。但如果將這些 uvm_fatal 替換為 uvm_error，將所有類似的問題一次暴露出來，一次性修復，這會極大縮減時間，提高效率。
## phase 跳轉
在之前的所有表述中，各個 phase 都是順序執行的，前一個 phase 執行完才執行後一個。但是並沒有介紹過當後一個 phase 執行後還可以再執行一次前面的 phase。而「跳轉」這個字則完全打破了這個觀念：phase 之間可以互相跳來跳去。  
EX: 實作 main_phase 到 reset_phase 的跳轉  
    假如在驗證平台中監測到 reset_n 訊號為低電平，則馬上從 main_phase 跳到 reset_phase。driver的程式碼如下：
```
task my_driver::reset_phase(uvm_phase phase);
  phase.raise_objection(this);
  `uvm_info("driver", "reset phase", UVM_LOW)
  vif.data <= 8'b0;
  vif.valid <= 1'b0;
  while(!vif.rst_n)
    @(posedge vif.clk);
  phase.drop_objection(this);
endtask

task my_driver::main_phase(uvm_phase phase);
  `uvm_info("driver", "main phase", UVM_LOW)
  fork
    while(1) begin
      seq_item_port.get_next_item(req);
      drive_one_pkt(req);
      seq_item_port.item_done();
    end
    begin
      @(negedge vif.rst_n);
      phase.jump(uvm_reset_phase::get());     // 跳轉到 reset phase
    end
  join
endtask
```
reset_phase 主要做一些清理工作，並等待重設完成。 main_phase 中一旦監測到 reset_n 為低電平，則馬上跳到 reset_phase。
在 top_tb 中，控制重設訊號代碼如下：
```
initial begin
  rst_n = 1'b0;
  #1000;
  rst_n = 1'b1;
  #3000;
  rst_n = 1'b0;
  #3000;
  rst_n = 1'b1;
end
```
在 my_case 中控制 objection 程式碼如下：
```
task my_case0::reset_phase(uvm_phase phase);
  `uvm_info("case0", "reset_phase", UVM_LOW)
endtask

task my_case0::main_phase(uvm_phase phase);
  phase.raise_objection(this);
  `uvm_info("case0", "main_phase", UVM_LOW)
  #10000;
  phase.drop_objection(this);
endtask
```
Output:
```
# UVM_INFO my_case0.sv(15) @ 0: uvm_test_top [case0] reset_phase
# UVM_INFO my_driver.sv(25) @ 0: uvm_test_top.env.i_agt.drv [driver] reset phase
# UVM_INFO my_case0.sv(20) @ 1100: uvm_test_top [case0] main_phase
# UVM_INFO my_driver.sv(34) @ 1100: uvm_test_top.env.i_agt.drv [driver] main phase
# UVM_INFO /home/landy/uvm/uvm-1.1d/src/base/uvm_phase.svh(1314) @ 4000: repo-rter[PH_JUMP] phase main # UVM_WARNING @ 4000: main_objection [OBJTN_CLEAR] Object 'uvm_top' cleared
ob jection counts for main_objection
# UVM_INFO my_case0.sv(15) @ 4000: uvm_test_top [case0] reset_phase
# UVM_INFO my_driver.sv(25) @ 4000: uvm_test_top.env.i_agt.drv [driver] reset phase
# UVM_INFO my_case0.sv(20) @ 7100: uvm_test_top [case0] main_phase
# UVM_INFO my_driver.sv(34) @ 7100: uvm_test_top.env.i_agt.drv [driver] main phase
```
很明顯，整個驗證平台都從 main_phase 跳到了 reset_phase。在上述運行結果中，出現了一個 UVM_WARNING。這是因為在 my_driver 中呼叫 jump時，並沒有把 my_case0 中提起的 objection 進行撤銷。加入跳轉後，整個驗證平台 phase 的運行圖實作變成如圖所示形式。
<img width="899" height="756" alt="image" src="https://github.com/user-attachments/assets/7845de7a-8d33-4e92-a355-593e5ed26b24" />

圖中灰色區域的 phase 在整個運行圖中出現了兩次。跳轉中最難的地方在於跳轉前後的清理和準備。如上面的運行結果中的警告訊息就是因為沒有及時對 objection 進行清理。對 scoreboard 來說，這個問題可能尤其嚴重。在跳轉前，scoreboard 的 expect_queue 中的資料應該會清空，同時要容忍跳轉後 DUT 可能輸出一些異常資料。在 my_driver 中使用了 jump 函數，它的原型是：
```
function void uvm_phase::jump(uvm_phase phase);
```
jump 函數的參數必須是一個 uvm_phase 類型的變數。在 UVM 中，這樣的變數共有如下幾個：
```
uvm_build_phase::get();
uvm_connect_phase::get();
uvm_end_of_elaboration_phase::get();
uvm_start_of_simulation_phase::get();
uvm_run_phase::get();
uvm_pre_reset_phase::get();
uvm_reset_phase::get();
uvm_post_reset_phase::get();
uvm_pre_configure_phase::get();
uvm_configure_phase::get();
uvm_post_configure_phase::get();
uvm_pre_main_phase::get();
uvm_main_phase::get();
uvm_post_main_phase::get();
uvm_pre_shutdown_phase::get();
uvm_shutdown_phase::get();
uvm_post_shutdown_phase::get();
uvm_extract_phase::get();
uvm_check_phase::get();
uvm_report_phase::get();
uvm_final_phase::get();
```
但並不是所有的 phase 都可以當作 jump 的參數。如果將 jump 的參數替換為 uvm_build_phase：：get（），那麼執行驗證平台後會給出以下結果：
```
UVM_FATAL /home/landy/uvm/uvm-1.1d/src/base/uvm_root.svh(922) @ 4000: reporte r [RUNPHSTIME] The run phase
```
所以往前跳到從 build 到 start_of_simulation 的 function phase 是不可行的。如果把參數替換為 uvm_run_phase：：get（），也是
不可行的
```
UVM_FATAL /home/landy/uvm/uvm-1.1d/src/base/uvm_phase.svh(1697) @ 4000: reporte r [PH_BADJUMP] phase run
```
UVM 會提示出 **run_phase 不是 main_phase 的先驅 phase 或是後繼 phase**。這非常容易理解。run_phase 是與 12 個動態運行的 phase 並行運行的，不存在任何先驅或後繼的關係。
那麼哪些 phase 可以作為 jump 的參數呢？ **uvm_pre_reset_phase：：get（）後的所有 phase 都可以**
* **向前跳轉**
  * 如從 main_phase 跳到 reset_phase
  * 只能是 main_phase 前的動態運行 phase 中的一個。
* **向後跳轉**
  * 如從 main_phase 跳到 shutdown_phase
  * 除了動態運行的 phase 外，還可以是函數 phase，如可以從 main_phase 跳到 final_phase
## phase 調適
UVM 提供命令列參數 UVM_PHASE_TRACE 來對 phase 機制進行偵錯，其使用方式為：
```
<sim command> +UVM_PHASE_TRACE
```
```
# UVM_INFO /home/landy/uvm/uvm-1.1d/src/base/uvm_phase.svh(1124) @ 0: reporter [PH/TRC/STRT] Phase 'uvm.
# UVM_INFO /home/landy/uvm/uvm-1.1d/src/base/uvm_phase.svh(1203) @ 0: reporter [PH/TRC/SKIP] Phase 'uvm.
# UVM_INFO /home/landy/uvm/uvm-1.1d/src/base/uvm_phase.svh(1381) @ 0: reporter [PH/TRC/DONE] Phase 'uvm.
# UVM_INFO /home/landy/uvm/uvm-1.1d/src/base/uvm_phase.svh(1403) @ 0: reporter [PH/TRC/SCHEDULED] Phase
# UVM_INFO /home/landy/uvm/uvm-1.1d/src/base/uvm_phase.svh(1124) @ 0: reporter [PH/TRC/STRT] Phase 'uvm.
# UVM_INFO /home/landy/uvm/uvm-1.1d/src/base/uvm_phase.svh(1203) @ 0: reporter [PH/TRC/SKIP] Phase 'uvm.
# UVM_INFO /home/landy/uvm/uvm-1.1d/src/base/uvm_phase.svh(1381) @ 0: reporter [PH/TRC/DONE] Phase 'uvm.
```
## 超時退出
在驗證平台運行時，有時測試案例會出現掛起（hang up）的情況。在這種狀態下，仿真時間一直往前走，driver 或 monitor 並沒有發出或收到 transaction，也沒有 UVM_ERROR 出現。一個測試案例的運行時間是可以預期的，如果超出了這個時間，那麼通常就是出錯了。在 UVM 中透過 uvm_root 的 set_timeout 函數可以設定逾時時間：
```
function void base_test::build_phase(uvm_phase phase);
         super.build_phase(phase);
         env = my_env::type_id::create("env", this);
         uvm_top.set_timeout(500ns, 0);
endfunction
```
* set_timeout 函數有兩個參數
  * 第一個參數是設定的時間
  * 第二個參數表示此設定是否可以被其後的其他 set_timeout 語句覆蓋
    * 如上的程式碼將逾時的時間定為 500ns。如果達到 500ns 時，測試案例還沒有運行完畢，則會給出一條 uvm_fatal 的提示訊息，並退出仿真。預設的超時退出時間是 9200s，是透過宏 UVM_DEFAULT_TIMEOUT 來指定的：
```
`define UVM_DEFAULT_TIMEOUT 9200s
```
還可以在命令列中設定：
```
<sim command> +UVM_TIMEOUT=<timeout>,<overridable>
```
其中 timeout 是要設定的時間，overridable 表示能否被覆蓋，其值可以是 YES 或 NO。如將超時退出時間設定為 300ns，且可被覆蓋，程式碼如下：
```
<sim command> +UVM_TIMEOUT="300ns, YES"
```
## objection 機制
## objection 與 task phase
* 在進入某一 phase 時，UVM 會收集此 phase 提出的所有 objection，並且實時監測所有 objection 是否已經被撤銷了，當發現所有都已經撤銷後，那麼就會關閉此 phase，開始進入下一個 phase。當所有的 phase 都執行完畢後，就會呼叫 $finish 來將整個的驗證平台關掉
* 如果 UVM 發現此 phase 沒有提起任何 objection，那麼將會直接跳到下一個 phase。假如驗證平台中只有（注意「只有」兩個字）driver 中提起了異議，而 monitor 等都沒有提起，很顯然，driver 中的程式碼是可以執行的，那麼 monitor 中的程式碼能夠執行嗎？答案是肯定的。當進入 monitor 後，系統會監測到已經有 objection 被提起了，所以會執行 monitor 中的程式碼。當過了 100 個單位時間之後，driver 中的 objection 被撤銷。此時，UVM 監測發現所有的 objection 都被撤銷了（因為只有 driver raise_objection），於是 UVM 會直接「殺死」monitor 中的無限循環進程，並且跳到下一個 phase，即 post_main_phase（）。假設進入 main_phase 的時刻為 0，那麼進入 post_main_phase 的時刻就為 100。
* 如果 driver 根本沒有 raise_objection，而且所有其他 component 的 main_phase 裡面也沒有 raise_objection，那麼在進入 main_phase 時，UVM 發現沒有任何 objection 被提起，於是雖然 driver 中有一個延時 100 個單位時間的程式碼，monitor 中有一個無限循環，UVM 也都不理會，它會直接跳到 post_main_phase，假設進入 main_phase 的時刻為 0，那麼進入 post_main_phase 的時刻還是為 0
* UVM 使用者一定要注意：如果想要執行一些耗費時間的程式碼，那麼要在此 phase 下任一個 component 中至少提起一次 objection
* 上述結論只適用於 12 個 run-time 的 phase。對於 run_phase 則不適用。由於 run_phase 與動態運行的 phase 是並行運行的，如果 12 個動態運行的 phase 有 objection 被提起，那麼 run_phase 根本不需要 raise_objection 就可以自動執行
   * 第一個是其他動態運行的 phase 中有 objection 被提起。在這種情況下，運行時間受其他動態運行 phase 中 objection 控制，run_phase 只能被動地接受
   * 第二是在 run_phase 中 raise_objection。這種情況下運行時間完全受 run_phase 控制\
<img width="515" height="754" alt="image" src="https://github.com/user-attachments/assets/433a0dee-53aa-4473-9cf9-645ee4ed484e" />

如圖所示為一個 env 與 model、scb 組成的大樓，每一層就是一個 phase（為了方便起見，圖中並沒有將 12 個動態運作的 phase
全部列出，而只列出了 reset_phase 等 4 個 phase）。這棟建築物的每一層都有三個房間，其中最外層最大的就是 env，而其中又包含
了 model 與 scb 兩個房間，換句話說，由於 env 是 model 和 scb 的父結點，所以 model 與 scb 房間其實是房中房。在 env、model、scb 三個
房間中，分別有一個歷史遺留的井 run_phase（OVM 遺留的），可以直通樓頂。
在每層的每個房間及各個房間的井中，都有可能存在著殭屍（objection）及需要通電才能運轉的機器（在每個phase中寫的代
碼）。整大樓處於斷電的狀態。
有一棵叫UVM的植物，在經歷start_of_simulation_phase之後，於0時刻進入到最頂層（12層）：pre_reset_phase。在進入後，
它首先為本層所有房間及所有井（run_phase）通電，如果房間及井中有機器，那麼這些機器就會運轉起來。
這棵植物在通電完畢後開始檢測各個房間中有沒有殭屍（是否raise_objection），如果任一個房間中有殭屍，那麼就開始消
滅這些殭屍，一直到所有殭屍消失（drop_objection）。當所有的殭屍被消滅後，它就斷掉這一層各房間的電，所有正在運作的
機器將會停止運轉，然後這棵UVM植物進入下一層。要注意的是，它只會斷掉所有房間的電，而沒有斷掉所有的井（run_phase）
中的電，所以各個井中如果有機器，那麼它們仍然在正常運作。
如果所有的房間中都沒有殭屍，那麼它直接斷電並進入下一層，在這種情況下，所有的機器只發出一聲轟鳴聲，便被緊急終
止了。這棵UVM植物一層一層消滅殭屍，一直到消滅底層post_shutdown_phase中的殭屍。此時，12個動態運行phase全部結束，
它們中的殭屍全部被消滅完畢。這棵UVM植物並不是立即進入extract_phase，而是開始查看所有的井（run_phase）中是否有僵
屍，如果有那麼就開始消滅它們，一直到所有的殭屍消失，否則直接斷掉井中的電，所有井中正在運轉的機器停止運轉。當
run_phase中的殭屍也被消滅完畢後，開始進入extract_phase。
所以，欲使每一層中的機器（代碼）運轉起來，只要在這一層的任何一個房間（任一component）中加入一個殭屍
（raise_objection）即可。如果殭屍永遠無法消失（phase.raise_objection與phase.drop_objection之間是一個無限循環），那麼就會一
直停留在這一層。
