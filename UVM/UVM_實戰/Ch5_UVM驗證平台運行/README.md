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
在圖3-2中，除了兄弟關係的component，還有一種叔侄關係的component，如my_scoreboard與my_driver，從樹的層次結構上
來說，scoreboard等級是高於driver的，但是，這兩者build_phase的執行順序其實也是不確定的。這兩者的執行順序除了上節提到的
字典序外，也用到了圖論中樹的遍歷方式：廣度優先或是深度優先。
所謂廣度優先，指的是如果i_agt的build_phase執行完畢後，接下來執行的是其兄弟component的build_phase，當所有兄弟的
build_phase執行完畢後，再執行其孩子的build_phase。
所謂深度優先，指的是如果i_agt的build_phase執行完畢後，它接下來執行的是其孩子的build_phase，如果孩子還有孩子，那麼
再繼續執行下去，一直到整棵以i_agt為樹根的UVM子樹的build_phase執行完畢，之後再執行i_agt的兄弟的build_phase。
UVM中採用的是深度優先的原則，對於圖3-2中的scoreboard及driver的build_phase的執行順序，i_agt實例化時名字為“i_agt”，
而scb為“scb”，那麼i_agt的build_phase先執行，在執行完畢後，接下來執行driver、monitor及sequencer的build_phase。當全部執行完
畢後再執行scoreboard的build_phase：
