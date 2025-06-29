# UVM 中的路徑
## get_full_name 函式
* 一個 component（如 my_driver）內透過 get_full_name 函式可以得到此 component 的路徑
```
function void my_driver::build_phase();
  super.build_phase(phase);
  $display("%s", get_full_name());
endfunction
```
ch2 的層次結構中的 my_driver 中，那麼印出來的值就是 **uvm_test_top.env.i_agt.drv**  
![image](https://github.com/user-attachments/assets/a8020746-ef76-41de-b702-40e1ac0e4aa4)
* uvm_test_top 實例化時的名字是 uvm_test_top，這個名字是由 UVM 在 run_test 時自動指定的
* uvm_top 的名字是 __top__，但是在顯示路徑的時候，並不會顯示出這個名字，而**只顯示從 uvm_test_top 開始的路徑**
## set 與 get 函數的參數
* config_db 機制用於在 UVM 驗證平台間傳遞參數
* set 函數是寄信，而 get 函數是收信，它們通常都是成對出現的
```
uvm_config_db#(int)::set(this, "env.i_agt.drv", "pre_num", 100);
```
* 第一個和第二個參數聯合起來組成**目標路徑**，與此路徑符合的目標才能收信
  * 第一個參數必須是一個 uvm_component 實例的指針
  * 第二個參數是相對此實例的路徑
* 第三個參數表示一個記號，用以說明這個值是傳給目標中的哪個成員的
* 第四個參數是要設定的值
在 driver 中的 build_phase 使用以下方式收信
```
uvm_config_db#(int)::get(this, "", "pre_num_max", pre_num_max);  // 最推薦
或者：
uvm_config_db#(int)::get(this.parent, "drv", "pre_num_max", pre_num_max);
或者：
uvm_config_db#(int)::get(null, "uvm_test_top.env.i_agt.drv", "pre_num_max", p re_num_max);    // 絕對路徑
```
* **get 函數**
  * 一般的，如果第一個參數被設定為 this，那麼第二個參數可以是一個空的字串，指當前的 component
  * 第三個參數就是 set 函數中的第三個參數
  * 第四個參數則是要設定的變數
**PS**: 在 top_tb 中透過 config_db 機制的 set 函數設定 virtual interface 時，set 函數的第一個參數為 null。在這種情況下，
UVM 會自動把第一個參數替換為 uvm_root：：get（），即 uvm_top。換句話說，以下兩種寫法是完全等價的：
```
initial begin
  uvm_config_db#(virtual my_if)::set(null, "uvm_test_top.env.i_agt.drv", "vif", input_if);
end

initial begin
  uvm_config_db#(virtual my_if)::set(uvm_root::get(), "uvm_test_top.env.i_ag t. drv", "vif", input_if);
end
```
## 省略 get 語句
* set 與 get 函數一般都是成對出現，**但在某些情況下，是可以只有 set 而沒有 get 語句**，也就是省略 get 語句。
在 3.1.5 節介紹到與 uvm_component 相關的巨集時，曾經提及 field automation 機制與 uvm_component 機制的結合。
假設在 my_driver 中有成員變數 pre_num，把其使用 uvm_field_int 實作 field automation 機制：
```
int pre_num;

// field automation 機制
`uvm_component_utils_begin(my_driver)
`uvm_field_int(pre_num, UVM_ALL_ON)
`uvm_component_utils_end

function new(string name = "my_driver", uvm_component parent = null);
  super.new(name, parent);
  pre_num = 3;
endfunction

virtual function void build_phase(uvm_phase phase);
  `uvm_info("my_driver", $sformatf("before super.build_phase, the pre_num is %0d", pre_num), UVM_LOW)  // 呼叫 super.build_phase() config db 應該還沒設定進去
  super.build_phase(phase);
  `uvm_info("my_driver", $sformatf("after super.build_phase, the pre_num is %0d", pre_num), UVM_LOW)   // 呼叫後，無須 get db 可以直接 get 設定完的值
  if(!uvm_config_db#(virtual my_if)::get(this, "", "vif", vif))
    `uvm_fatal("my_driver", "virtual interface must be set for vif!!!")
endfunction
```
* **只要使用 uvm_field_int 註冊，並且在 build_phase 中呼叫 super.build_phase()，就可以省略在 build_phase 中的 get 語句**
  uvm_config_db#(int)::get(this, "", "pre_num", pre_num);
* 這裡的關鍵是 build_phase 中的 super.build_phase 語句，當執行到 driver 的 super.build_phase 時，會自動執行 get 語句
  * 第一，my_driver 必須使用 uvm_component_utils 巨集註冊
  * 第二，pre_num 必須使用 uvm_field_int 巨集註冊
  * 第三，在呼叫 set 函數的時候，set 函數的第三個參數必須與要 get 函數中變數的名字一致，也就是必須是 pre_num
    * 所以上節中，雖然說這兩個參數可以不一致，但是**最好的情況還是一致**
* **對於 set 語句，則沒有辦法省略**
## 跨層次的多重設置
在前面的所有例子中，都是設定一次，取得一次。但是假如設定多次，只取得一次，最後會得到哪個數值呢？
假如 uvm_test_top 和 env 中都對 driver 的 pre_num 的值進行了設置，在 uvm_test_top 中的設置語句如下：
```
文件：src/ch3/section3.5/3.5.4/normal/my_case0.sv
function void my_case0::build_phase(uvm_phase phase);
    super.build_phase(phase);
…
    uvm_config_db#(int)::set(this,
    "env.i_agt.drv",
    "pre_num",
    999);
    `uvm_info("my_case0", "in my_case0, env.i_agt.drv.pre_num is set to 999",UVM_LOW)
```
在 env 的設定語句如下：
```
文件：src/ch3/section3.5/3.5.4/normal/my_env.sv
virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
…
      uvm_config_db#(int)::set(this,
      "i_agt.drv",
      "pre_num",
      100);
      `uvm_info("my_env", "in my_env, env.i_agt.drv.pre_num is set to 100",UVM_LOW)
endfunction
```
UVM 規定層次越高，那麼它的優先權就越高，所以 driver 獲取的值為 999
* 越靠近根結點 uvm_top，則認為其層次越高
* uvm_test_top 的層次是高於 env 的，所以 uvm_test_top 中的 set 函數的優先權高
**為甚麼這樣設計?**
相對於 env 來說，uvm_test_top（my_case）更接近使用者。用戶會在 uvm_test_top 中設定不同的 default_sequence，從而衍生出許多不同的測試用例來。而對於 env，它在 uvm_test_top 中實例化。有時候，這個 env 根本就不是用戶自己開發的，很可能是別人已經開發好的一個非常成熟的可重複使用的模組。對於這種成熟的模組，如果覺得其中某些參數不合要求，那麼要到 env 中去修改相關的參數嗎？顯然這是不合理的。比較合理的就是在uvm_test_top 的 build_phase 中透過 set 函數的方式修改。所以說，UVM 這種看似勢利的行為其實極大方便了用戶的使用。
上述結論在 set 函數的第一個參數為 this 時是成立的，但是假如 set 函數的第一個參數不是 this 會如何呢？假設 uvm_test_top 的 set 語句是:
```
function void my_case0::build_phase(uvm_phase phase);
  super.build_phase(phase);

  uvm_config_db#(int)::set(uvm_root::get(),
                           "uvm_test_top.env.i_agt.drv",
                           "pre_num",
                           999);

  `uvm_info("my_case0", "in my_case0, env.i_agt.drv.pre_num is set to 999", UVM_LOW)
endfunction
```
env 的 set 語句改成:
```
virtual function void build_phase(uvm_phase phase);
  super.build_phase(phase);

  uvm_config_db#(int)::set(uvm_root::get(),
                           "uvm_test_top.env.i_agt.drv",
                           "pre_num",
                           100);

  `uvm_info("my_env", "in my_env, env.i_agt.drv.pre_num is set to 100", UVM_LOW)
endfunction
```
在這種情況下，driver 得到的 pre_num 的值是 100。由於 set 函數的第一個參數是 uvm_root：：get（），所以寄信人變成了 uvm_top。在這種情況下，只能比較寄信的時間。 UVM 的 build_phase 是由上而下執行的，my_case0 的 build_phase 先於 my_env 的 build_phase 執行。所以 my_env 對pre_num 的設定在後，其設定成為最終的設定。
假如 uvm_test_top 中 set 函數的第一個參數是 this，而 env 中 set 函數的第一個參數是uvm_root：：get（），那麼driver得到的 pre_num 的值也是 100。這是因為 env 中 set 函數的寄信者變成了 uvm_top，在 UVM 樹中具有最高的優先權。
因此，無論如何，在呼叫 set 函數時其第一個參數應該盡量使用 this。在無法取得 this 指標的情況下（如在top_tb中），使用 null 或 uvm_root：：get（）
## 同一層次的多重設定
