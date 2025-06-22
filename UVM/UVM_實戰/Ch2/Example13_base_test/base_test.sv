/*
    實際應用的 UVM 驗證平台中，my_env 並不是樹根，通常來說，樹根是一個基於 uvm_test 衍生的類別。本節先講述 base_test，
    真正的測試案例都是基於 base_test 派生的一個類別。
*/
class base_test extends uvm_test;

  my_env env;

  function new(string name = "base_test", uvm_component parent = null);
    super.new(name,parent);
  endfunction

  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void report_phase(uvm_phase phase);

  `uvm_component_utils(base_test)                                       // 使用 uvm_component_utils 巨集來註冊到 factory 中

endclass


function void base_test::build_phase(uvm_phase phase);
  super.build_phase(phase); 
  env = my_env::type_id::create("env", this);                           // 在 build_phase 中實例化 my_env
  uvm_config_db#(uvm_object_wrapper)::set(this,                         // 設定 sequencer 的 default_sequence
                                          "env.i_agt.sqr.main_phase",
                                          "default_sequence",
                                          my_sequence::type_id::get());
endfunction

// report_phase 也是 UVM 內建的一個 phase，它在 main_phase 結束之後執行
/*
  在 report_phase 中根據 UVM_ERROR 的數量來列印不同的資訊。
  有些日誌分析工具可以根據列印的資訊來判斷 DUT 是否通過了某個測試案例的檢查
*/
function void base_test::report_phase(uvm_phase phase);
  uvm_report_server server;
  int err_num;

  super.report_phase(phase);

  server = get_report_server();
  err_num = server.get_severity_count(UVM_ERROR);

  if (err_num != 0) begin
    $display("TEST CASE FAILED");
  end
  else begin
    $display("TEST CASE PASSED");
  end
endfunction

/*
    通常在base_test中也做以下事情：
      第一，設定整個驗證平台的逾時退出時間；
      第二，透過 config_db 設定驗證平台中某些參數的值。
    這些根據不同的驗證平台及不同的公司而不同，沒有統一的答案。
*/