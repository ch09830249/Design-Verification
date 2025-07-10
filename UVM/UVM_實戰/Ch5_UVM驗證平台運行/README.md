# Phase 機制
## task phase 與 function phase
* phase 依照其是否消耗模擬時間（$time列印出的時間）的特性，可以分成兩大類
  * **function phase**，如 build_phase、connect_phase 等，這些 phase 都不耗費模擬時間，透過**函數**來實現
  * **task phase**，如run_phase等，它們耗費仿真時間，透過**任務**來實現
給 DUT 施加激勵、監測 DUT 的輸出都是在這些 phase 中完成的。灰色背景所示的是 task phase，其他為 function phase
<img width="1205" height="671" alt="image" src="https://github.com/user-attachments/assets/620018a4-584f-43bf-884e-fe2fb19f2541" />
上述所有的 phase 都會依照圖中的順序**自上而下自動執行**
```
class my_case0 extends base_test;
  string tID = get_type_name();
  …

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info(tID, "build_phase is executed", UVM_LOW)
  endfunction

  …

  virtual function void start_of_simulation_phase(uvm_phase phase);
    super.start_of_simulation_phase(phase);
    `uvm_info(tID, "start_of_simulation_phase is executed", UVM_LOW)
  endfunction

  virtual task run_phase(uvm_phase phase);
    `uvm_info(tID, "run_phase is executed", UVM_LOW)
  endtask

  virtual task pre_reset_phase(uvm_phase phase);
    `uvm_info(tID, "pre_reset_phase is executed", UVM_LOW)
  endtask

  …

  virtual task post_shutdown_phase(uvm_phase phase);
    `uvm_info(tID, "post_shutdown_phase is executed", UVM_LOW)
  endtask

  virtual function void extract_phase(uvm_phase phase);
    super.extract_phase(phase);
    `uvm_info(tID, "extract_phase is executed", UVM_LOW)
  endfunction
  …

  virtual function void final_phase(uvm_phase phase);
    super.final_phase(phase);
    `uvm_info(tID, "final_phase is executed", UVM_LOW)
  endfunction

endclass
```
執行上述程式碼，可以看到各 phase 被依序執行。對 function phase 來說，在同一時間只有一個 phase 在執行；但是 task phase 中，run_phase 和 pre_reset_phase 等 12 個小的 phase 並行運行。後者稱為動態運行（runtime）
的 phase。對於 task phase，從全域的觀點來看其順序大致如下：
```
// 2 個 thread
fork
  begin
    run_phase();
  end
  begin
    pre_reset_phase();
    reset_phase();
    post_reset_phase();
    pre_configure_phase();
    configure_phase();
    post_configure_phase();
    pre_main_phase();
    main_phase();
    post_main_phase();
    pre_shutdown_phase();
    shutdown_phase();
    post_shutdown_phase();
  end
join
```
## 動態運行 phase

## phase 執行順序
