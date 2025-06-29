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
## set_report_severity_action 函式
在上一節中，當 UVM_ERROR 達到一定數量時，可以自動退出模擬。在計數當中，是不含 UVM_WARNING 的。可以透過設定 set_report_severity_action 函式來把 UVM_WARNING 加入計數目標：
```
virtual function void connect_phase(uvm_phase phase);
      set_report_max_quit_count(5);
      env.i_agt.drv.set_report_severity_action(UVM_WARNING, UVM_DISPLAY|UVM_COUNT);    // 可以把 env.i_agt.drv 的 UVM_WARNING 加入計數目標中
…
endfunction
```
## set_report_severity_action_hier 函式
```
env.i_agt.set_report_severity_action_hier(UVM_WARNING, UVM_DISPLAY| UVM_COUNT);    // env.i_agt 及其下所有結點的 UVM_WARNING 加入計數目標中
```
在預設情況下，UVM_ERROR 已經加入了統計計數。如果要把其從統計計數目標中移除
```
env.i_agt.drv.set_report_severity_action(UVM_ERROR, UVM_DISPLAY);  // Only display
```
## set_report_id_action 函式
```
env.i_agt.drv.set_report_id_action("my_drv", UVM_DISPLAY| UVM_COUNT);
```
上述程式碼將 ID 為 my_drv 的所有資訊加入計數中，無論是 UVM_INFO，或是 UVM_WARNING 或是 UVM_ERROR、UVM_FATAL
## set_report_id_action_hier 函式
```
env.i_agt.set_report_id_action_hier("my_drv", UVM_DISPLAY| UVM_COUNT);    // set_report_id_action同樣有其遞歸呼叫方式
```
## set_report_severity_id_action 函式
UVM 還支援將它們聯合起來 (嚴重性和 ID) 進行設置
```
env.i_agt.drv.set_report_severity_id_action(UVM_WARNING, "my_driver", UVM_DISPLAY| UVM_COUNT);
```
## set_report_severity_id_action_hier 函式
```
env.i_agt.set_report_severity_id_action_hier(UVM_WARNING, "my_driver", UVM_DISPLAY| UVM_COUNT);
```
## 命令列中設定計數目標
格式
```
<sim command> +uvm_set_action=<comp>,<id>,<severity>,<action>
```
```
<sim command> +uvm_set_action="uvm_test_top.env.i_agt.drv, my_driver, UVM_NG, UVM_DISPLAY|UVM_COUNT"
```
對所有的 ID 設置，可以使用 _ALL_ 來代替 ID
```
<sim command> +uvm_set_action="uvm_test_top.env.i_agt.drv, _ALL_, UVM_WARNING, UVM_DISPLAY|UVM_COUNT"
```
# UVM 的斷點功能
* 在程式運作時，預先在某語句處設定一斷點。當程式執行到此處時，停止仿真，進入交互模式，從而進行調試。
* 斷點功能需要從模擬器的角度進行設置，不同模擬器的設置方式不同。為了消除這些設定方式的不同，UVM支援內建的斷點功能，執行到斷點時，自動停止仿真，進入互動模式
## UVM_STOP
```
virtual function void connect_phase(uvm_phase phase);
      env.i_agt.drv.set_report_severity_action(UVM_WARNING, UVM_DISPLAY| UVM_STOP);
…
endfunction
```
當 env.i_agt.drv 中出現 UVM_WARNING 時，立即停止仿真，進入交互模式。這裡用到了 set_report_severity_action 函數
只要將其中的 UVM_COUNT 替換為 UVM_STOP，就可以實現對應的斷點功能
## 命令列中設定 UVM 斷點
```
<sim command> +uvm_set_action="uvm_test_top.env.i_agt.drv,my_driver,UVM_WARNING,UVM_DISPLAY|UVM_STOP"
```
# 將輸出資訊導入文件中
* 預設情況下，UVM 會將 UVM_INFO 等資訊顯示在標準輸出（終端螢幕）上。各個仿真器提供將顯示在標準輸出的資訊同時輸出到一個日誌檔 (log) 中的功能。但是這個日誌檔混雜了所有的 UVM_INFO、UVM_WARNING、UVM_ERROR及UVM_FATAL。
* UVM 提供將特定資訊輸出到特定日誌檔案的功能
## set_report_severity_file 函式
```
UVM_FILE info_log;
UVM_FILE warning_log;
UVM_FILE error_log;
UVM_FILE fatal_log;

virtual function void connect_phase(uvm_phase phase);
  // 開檔案
  info_log = $fopen("info.log", "w");
  warning_log = $fopen("warning.log", "w");
  error_log = $fopen("error.log", "w");
  fatal_log = $fopen("fatal.log", "w");

  // 設定要寫入的檔案
  env.i_agt.drv.set_report_severity_file(UVM_INFO, info_log);
  env.i_agt.drv.set_report_severity_file(UVM_WARNING, warning_log);
  env.i_agt.drv.set_report_severity_file(UVM_ERROR, error_log);
  env.i_agt.drv.set_report_severity_file(UVM_FATAL, fatal_log);

  // UVM_LOG 記得要舉
  env.i_agt.drv.set_report_severity_action(UVM_INFO, UVM_DISPLAY | UVM_LOG);
  env.i_agt.drv.set_report_severity_action(UVM_WARNING, UVM_DISPLAY | UVM_LOG);
  env.i_agt.drv.set_report_severity_action(UVM_ERROR, UVM_DISPLAY | UVM_COUNT | UVM_LOG);
  env.i_agt.drv.set_report_severity_action(UVM_FATAL, UVM_DISPLAY | UVM_EXIT | UVM_LOG);
......
endfunction
```
將 env.i_agt.drv 的 UVM_INFO 輸出到 info.log，UVM_WARNING 輸出到 warning.log，UVM_ERROR 輸出到 error.log，UVM_FATAL 輸出到 fatal.log
## set_report_severity_action_hier 函式
```
// 將 env.i_agt 及其下所有結點的輸出資訊分類輸出到不同的日誌檔案中
env.i_agt.set_report_severity_file_hier(UVM_INFO, info_log);
env.i_agt.set_report_severity_file_hier(UVM_WARNING, warning_log);
env.i_agt.set_report_severity_file_hier(UVM_ERROR, error_log);
env.i_agt.set_report_severity_file_hier(UVM_FATAL, fatal_log);
env.i_agt.set_report_severity_action_hier(UVM_INFO, UVM_DISPLAY| UVM_LOG);
env.i_agt.set_report_severity_action_hier(UVM_WARNING, UVM_DISPLAY| UVM_LOG);
env.i_agt.set_report_severity_action_hier(UVM_ERROR, UVM_DISPLAY| UVM_COUNT |UVM_LOG);
env.i_agt.set_report_severity_action_hier(UVM_FATAL, UVM_DISPLAY| UVM_EXIT | UVM_LOG);
```
## set_report_id_file 函數
UVM 中也可以根據不同的 ID 來設定不同的日誌文件
```
UVM_FILE driver_log;
UVM_FILE drv_log;

virtual function void connect_phase(uvm_phase phase);
  driver_log = $fopen("driver.log", "w");
  drv_log = $fopen("drv.log", "w");

  env.i_agt.drv.set_report_id_file("my_driver", driver_log);
  env.i_agt.drv.set_report_id_file("my_drv", drv_log);

  env.i_agt.drv.set_report_id_action("my_driver", UVM_DISPLAY | UVM_LOG);
  env.i_agt.drv.set_report_id_action("my_drv", UVM_DISPLAY | UVM_LOG);
......
endfunction

virtual function void final_phase(uvm_phase phase);
  $fclose(driver_log);
  $fclose(drv_log);
endfunction
```
## set_report_id_action_hier 函式 (不贅述)
## set_report_severity_id_file 函式
```
UVM_FILE driver_log;
UVM_FILE drv_log;

virtual function void connect_phase(uvm_phase phase);
  driver_log = $fopen("driver.log", "w");
  drv_log = $fopen("drv.log", "w");

  env.i_agt.drv.set_report_severity_id_file(UVM_WARNING, "my_driver", driver_log);
  env.i_agt.drv.set_report_severity_id_file(UVM_INFO, "my_drv", drv_log);

  env.i_agt.drv.set_report_id_action("my_driver", UVM_DISPLAY | UVM_LOG);
  env.i_agt.drv.set_report_id_action("my_drv", UVM_DISPLAY | UVM_LOG);
endfunction
```
## set_report_severity_id_file_hier 函式 (不贅述)
# 控制列印訊息的行為
控制列印資訊行為系列函數 set_*_action 的典型應用。無論是 UVM_DISPLAY，還是 UVM_COUNT 或者是 UVM_LOG，都是 UVM 內部定義的一種行為
```
typedef enum
{
  UVM_NO_ACTION = 'b000000,
  UVM_DISPLAY = 'b000001,
  UVM_LOG = 'b000010,
  UVM_COUNT = 'b000100,
  UVM_EXIT = 'b001000,
  UVM_CALL_HOOK = 'b010000,
  UVM_STOP = 'b100000
} uvm_action_type;
```
不同的行為有不同的位偏移，所以不同的行為可以用「或」的方式組合在一起
```
UVM_DISPLAY| UVM_COUNT | UVM_LOG
```
* UVM_NO_ACTION 是不做任何操作
* UVM_DISPLAY 是輸出到標準輸出上
* UVM_LOG 是輸出到日誌檔案中，它能運作的前提是設定好了日誌檔
* UVM_COUNT 是作為計數目標
* UVM_EXIT 是直接退出模擬
* UVM_CALL_HOOK 是呼叫一個回調函數
* UVM_STOP 是停止仿真，進入命令列交互模式
在預設的情況下，UVM 設定瞭如下的行為：
```
set_severity_action(UVM_INFO, UVM_DISPLAY);
set_severity_action(UVM_WARNING, UVM_DISPLAY);
set_severity_action(UVM_ERROR, UVM_DISPLAY | UVM_COUNT);
set_severity_action(UVM_FATAL, UVM_DISPLAY | UVM_EXIT);
```
* 從 UVM_INFO 到 UVM_FATAL，都會輸出到標準輸出中
* UVM_ERROR 會作為模擬退出計數器的計數目標
* 出現 UVM_FATAL 時會自動退出模擬
透過設定為 UVM_NO_ACTION 來實現關閉某些資訊的輸出
```
virtual function void connect_phase(uvm_phase phase);
      env.i_agt.drv.set_report_severity_action(UVM_INFO, UVM_NO_ACTION);
endfunction
```
無論原本的冗餘度是什麼，經過上述設定後，env.i_agt.drv 的所有的 uvm_info 資訊都不會輸出
