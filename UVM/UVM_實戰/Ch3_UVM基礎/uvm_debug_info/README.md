# UVM 中列印資訊的控制
## 設定列印資訊的冗餘度閾值
```
typedef enum
{
  UVM_NONE = 0,
  UVM_LOW = 100,
  UVM_MEDIUM = 200,
  UVM_HIGH = 300,
  UVM_FULL = 400,
  UVM_DEBUG = 500
} uvm_verbosity;
```
* UVM 透過冗餘度等級的設定提高了模擬日誌的可讀性
* 在列印資訊之前，UVM 會比較要顯示資訊的冗餘度等級與預設的冗餘餘度閾值
  * **如果小於等於閾值，就會顯示，否則不會顯示**
* **預設的冗餘度閾值是 UVM_MEDIUM**，所有低於等於 UVM_MEDIUM（如 UVM_LOW）的資訊都會被印出來
## get_report_verbosity_level 函式
* **得到某個 component 的冗餘度閾值**如下
```
virtual function void connect_phase(uvm_phase phase);
    $display("env.i_agt.drv's verbosity level is %0d", env.i_agt.drv.get_report_verbosity_level());
endfunction
```
## set_report_verbosity_level 函數
* **設定某個特定 component 的預設冗餘度閾值**
  * 在 base_test 中將 driver 的冗餘度閾值設定為 UVM_HIGH（UVM_LOW、UVM_MEDIUM、UVM_HIGH 的資訊都會被印出）代碼為：
```
virtual function void connect_phase(uvm_phase phase);
        env.i_agt.drv.set_report_verbosity_level(UVM_HIGH);
…
endfunction
```
* 由於需要牽扯到**層次引用 (就是上面例子的路徑)**，所以**需要在 connect_phase 及以後的 phase 才能呼叫這個函數 (這樣各個 component 才都已經實例化)**  
* 如果不牽扯到任何層次引用，如設置目前 component 的冗餘度閾值，那麼可以在 connect_phase 之前呼叫
* 只對某個特定的component運作
## set_report_verbosity_level_hier 函數
* UVM 同樣提供遞歸的設定函數 set_report_verbosity_level_hier ，**如把 env.i_agt 及其下所有的 component 的冗餘度閾值設定為 UVM_HIGH 的代碼為**：
```
env.i_agt.set_report_verbosity_level_hier(UVM_HIGH);
```
## set_report_id_verbosity 函數
* set_report_id_verbosity 函數可以透過 ID 的設定冗餘度閾值
```
env.i_agt.drv.set_report_id_verbosity("ID1", UVM_HIGH);
```
這樣一來 uvm_info ID 為 ID1 的 log 就會受影響
```
// 經過設定後「ID1INFO」會顯示，但是「ID2INFO」不會顯示
`uvm_info("ID1", "ID1 INFO", UVM_HIGH)
`uvm_info("ID2", "ID2 INFO", UVM_HIGH)
```
## set_report_id_verbosity_hier 函數
* 這個函數同樣有其對應的遞歸呼叫函數
```
env.i_agt.set_report_id_verbosity_hier("ID1", UVM_HIGH);
```
## UVM 支援在命令列中設定冗餘度閾值
```
<sim command> +UVM_VERBOSITY=UVM_HIGH
或者：
<sim command> +UVM_VERBOSITY=HIGH
```
* 相當於在 base_test 中調用 set_report_verbosity_level_hier 函數，把 base_test 及以下所有 component 的冗餘度等級設定為UVM_HIGH
# 重載列印資訊的嚴重性
## set_report_severity_override 和 set_report_severity_id_override 函數
```
virtual function void connect_phase(uvm_phase phase);
        env.i_agt.drv.set_report_severity_override(UVM_WARNING, UVM_ERROR);
        // 重載嚴重性可以只針對某個 component 內的某個特定的 ID 來運作, 這裡是 my_driver
        //env.i_agt.drv.set_report_severity_id_override(UVM_WARNING, "my_driver", UVM_ERROR);
endfunction
```
假如在 my_driver 中有如下語句：
```
`uvm_warning("my_driver", "this information is warning, but prints as UVM_ERROR")
```
**Original Output**
```
UVM_WARNING my_driver.sv(29) @ 1100000: uvm_test_top.env.i_agt.drv [my_driver]this information is warning, but prints as UVM_ERROR
```
**After setting**
```
UVM_ERROR my_driver.sv(29) @ 1100000: uvm_test_top.env.i_agt.drv [my_driver] this information is warning, but prints as UVM_ERROR
```
## 重載嚴重性在命令列中實現
```
<sim command> +uvm_set_severity=<comp>,<id>,<current severity>,<new severity>
```
```
<sim command> +uvm_set_severity="uvm_test_top.env.i_agt.drv,my_driver, UVM_WARNING, UVM_ERROR"
// 同 env.i_agt.drv.set_report_severity_id_override(UVM_WARNING, "my_driver", UVM_ERROR);
```
若要設定所有的 ID，可以在 id 處使用 _ALL_：
```
<sim command> +uvm_set_severity="uvm_test_top.env.i_agt.drv,_ALL_,UVM_WARNING,UVM_ERROR"
```
# UVM_ERROR 到達一定數量結束仿真
* 當 uvm_fatal 出現時，表示出現了致命錯誤，模擬會馬上停止
* UVM 同樣支援 UVM_ERROR 達到一定數量時結束仿真。這個功能非常有用
* 對於某個測試案例，如果出現了大量的UVM_ERROR，根據這些錯誤已經可以確定bug所在了，再繼續模擬下去意義已經不大，此時就可以結束仿真，而不必等到所有的 objection 被撤銷
## set_report_max_quit_count 函數
```
function void base_test::build_phase(uvm_phase phase);
      super.build_phase(phase);
      env = my_env::type_id::create("env", this);
      set_report_max_quit_count(5);      // 當出現 5 個 UVM_ERROR 時，會自動退出
endfunction
```
```
# --- UVM Report Summary ---
##
Quit count reached!
# Quit count : 5 of 5
```
* 如果測試用例與 base_test 中同時設定了，則以測試用例中的設定為準
* 除了在 build_phase 之外，在其他 phase 設定也是可以的
## get_max_quit_count 函數
* 與 set_max_quit_count 相對應的是 get_max_quit_count，可以用來查詢目前的退出閾值
* 如果傳回值為 0 則表示無論出現多少個 UVM_ERROR 都不會退出仿真
## 命令列中設定退出閾值
```
<sim command> +UVM_MAX_QUIT_COUNT=6,NO
```
PS: 其中第一個參數 6 表示退出閾值，而第二個參數 NO 表示此值是不可以被後面的設定語句重載，其值還可以是 YES
# 設定計數的目標
