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
