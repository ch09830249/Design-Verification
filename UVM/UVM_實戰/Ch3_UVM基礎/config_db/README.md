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

  uvm_config_db#(int)::set(uvm_root::get(),        // 改這裡 (原本是 this)
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

  uvm_config_db#(int)::set(uvm_root::get(),        // 改這裡 (原本是 this)
                           "uvm_test_top.env.i_agt.drv",
                           "pre_num",
                           100);

  `uvm_info("my_env", "in my_env, env.i_agt.drv.pre_num is set to 100", UVM_LOW)
endfunction
```
在這種情況下，driver 得到的 pre_num 的值是 100。由於 set 函數的第一個參數是 uvm_root：：get（），所以寄信人變成了 uvm_top。在這種情況下，**只能比較寄信的時間**。 UVM 的 **build_phase 是由上而下執行的**，my_case0 的 build_phase 先於 my_env 的 build_phase 執行。所以 my_env 對pre_num 的設定在後，其設定成為最終的設定。
假如 uvm_test_top 中 set 函數的第一個參數是 this，而 env 中 set 函數的第一個參數是uvm_root：：get（），那麼 driver 得到的 pre_num 的值也是 100。這是因為 env 中 set 函數的寄信者變成了 uvm_top，在 UVM 樹中具有最高的優先權。
因此，無論如何，在呼叫 set 函數時其第一個參數應該盡量使用 this。在無法取得 this 指標的情況下（如在 top_tb 中），使用 null 或 uvm_root：：get（）
## 同一層次的多重設定
當跨層次來看問題時，是高層次的 set 設定優先；當處於同一層次時，上節已經提過，**是時間優先**
pre_num 在 99% 的測試案例中的值都是 7，只有在 1% 的測試案例中才會是其他值
```
class case1 extends base_test;
      function void build_phase(uvm_phase phase);
              super.build_phase(phase);
              uvm_config_db#(int)::set(this, "env.i_agt.drv", pre_num_max, 7);
      endfunction
endclass
…
class case99 extends base_test;
      function void build_phase(uvm_phase phase);
              super.build_phase(phase);
              uvm_config_db#(int)::set(this, "env.i_agt.drv", pre_num_max, 7);
      endfunction
endclass
class case100 extends base_test;
      function void build_phase(uvm_phase phase);
              super.build_phase(phase);
              uvm_config_db#(int)::set(this, "env.i_agt.drv", pre_num_max, 100);
      endfunction
endclass
```
前面 99 個測試案例的 build_phase 裡面都是相同的語句，這種程式碼維護起來非常困難。相當耗時的，而且是極易出錯的。
驗證中寫程式的一個原則是同樣的語句只在一個地方出現，盡量避免在多個地方出現。
A: 解決這個問題的方法就是在 base_test 的 build_phase 中使用 config_db：：set 進行設置，這樣，當由 base_test 派生而來的 case1～case99 在執行 super.build_phase（phase）時，都會進行設定：
```
classs base_test extends uvm_test;
      function void build_phase(uvm_phase phase);
              super.build_phase(phase);
              uvm_config_db#(int)::set(this, "env.i_agt.drv", pre_num_max, 7);
      endfunction
endclass
class case1 extends base_test;
      function void build_phase(uvm_phase phase);
              super.build_phase(phase);
      endfunction
endclass
…
class case99 extends base_test;
      function void build_phase(uvm_phase phase);
              super.build_phase(phase);
      endfunction
endclass
```
但是對於第 100 個測試用例，則依然需要這麼寫：
```
class case100 extends base_test;
      function void build_phase(uvm_phase phase);
              super.build_phase(phase);
              uvm_config_db#(int)::set(this, "env.i_agt.drv", pre_num_max, 100);
      endfunction
endclass
```
case100 的 build_phase 相當於如下所示連續設定了兩次：
```
uvm_config_db#(int)::set(this, "env.i_agt.drv", "pre_num", 7);
uvm_config_db#(int)::set(this, "env.i_agt.drv", "pre_num", 100);
```
## 非直線的設定與獲取
driver 的路徑為 uvm_test_top.env.i_agt.drv
* 在 uvm_test_top，env 或 i_agt 中，對 driver 中的某些變量透過 config_db 機制進行設置，稱為**直線的設定** (對其之下的 component 做設定)
* 若在其他 component，如 scoreboard 中，對 driver 的某些變數使用 config_db 機制進行設置，則稱為**非直線的設置**  (旁系的 component 做設定)
* 在 my_driver 中使用 config_db：：get 取得其他任意 component 設定給 my_driver 的參數，稱為**直線的取得**  (取得設定給自己的變數)
* 假如要在其他的 component，如在 reference model 中取得其他 component 設定給 my_driver 的參數的值，稱為**非直線的取得** (取得設定給別人的變數)
## 非直線的設置
**要進行非直線的設置，需要仔細設定 set 函數的第一個和第二個參數**
以在 scoreboard 中設定 driver 中的 pre_num 為例：
```
function void my_scoreboard::build_phase(uvm_phase phase);
    …
    uvm_config_db#(int)::set(this.m_parent,    // 先推到 scoreboard 的上一層共同的 parent component (env)
                              "i_agt.drv",     // 再指派到 agent 中的 driver 去做設定
                              "pre_num",
                              200);
    `uvm_info("my_scoreboard", "in my_scoreboard, uvm_test_top.env.i_agt.drv.pre_num is set to 200", UVM_LOW)
endfunction
```
或者：
```
function void my_scoreboard::build_phase(uvm_phase phase);
          super.build_phase(phase);
          uvm_config_db#(int)::set(uvm_root::get(),  // 先推到 root
          "uvm_test_top.env.i_agt.drv",              // 再一路從 uvm_test_top => env => agent => driver
          "pre_num",
          200);
endfunction
```

無論哪種方式，都帶來了一個新的問題。  
在 UVM 樹中，build_phase 是由上而下執行的，但 scb 與 i_agt 處於同一層級中，UVM 並沒有明文指出同一層級的 build_phase 的執行順序。所以當my_driver 在取得參數值時，my_scoreboard 的 **build_phase 可能已經執行了，也可能沒有執行**。所以，這種非直線的設置，會有一定的風險，應該避免這種情況的出現。
## 非直線的獲取
非直線的獲取也只需要設定其第一和第二個參數。假如要在 reference model 中取得 driver 的 pre_num 的值：
```
function void my_model::build_phase(uvm_phase phase);
    super.build_phase(phase);
    port = new("port", this);
    ap = new("ap", this);
    `uvm_info("my_model", $sformatf("before get, the pre_num is %0d", drv_pre_num), UVM_LOW)
    void'(uvm_config_db#(int)::get(this.m_parent, "i_agt.drv", "pre_num", drv_pre_num));      // 一樣推到共同的 parent component (env)
    `uvm_info("my_model", $sformatf("after get, the pre_num is %0d", drv_pre_num), UVM_LOW)
endfunction
```
或者：
```
void'(uvm_config_db#(int)::get(uvm_root::get(), "uvm_test_top.env.i_agt.drv", "pre_num", drv_pre_num));  // 一樣直接推到 root
```
非直線的取得可以在某些情況下避免 config_db：：set 的冗餘。上面的範例在 reference model 中取得 driver 的 pre_num 的值，如果不這樣做，而採用直線取得的方式，那麼需要在測試案例中透過 cofig_db：：set 分別給 reference model 和 driver 設定 pre_num 的值。
同樣的參數值設定出現在不同的兩個語句中，這大大增加了出錯的可能性。因此，非直線的獲取可以在驗證平台中多個元件（UVM樹結點）需要使用同一個參數時，減少config_db：：set的冗餘。
## config_db 機制對通配符的支持
在先前所有的範例使用完整路徑設定 virtual interface 的程式碼如下：
```
initial begin
      uvm_config_db#(virtual my_if)::set(null, "uvm_test_top.env.i_agt.drv", "vif",input_if);
      uvm_config_db#(virtual my_if)::set(null, "uvm_test_top.env.i_agt.mon", "vif",input_if);
      uvm_config_db#(virtual my_if)::set(null, "uvm_test_top.env.o_agt.mon", "vif",output_if);
end
```
使用通配符，可以把第一和第二個 set 語句合併為一個 set：
```
initial begin
      uvm_config_db#(virtual my_if)::set(null, "uvm_test_top.env.i_agt*", "vif", input_if);
      uvm_config_db#(virtual my_if)::set(null, "uvm_test_top.env.o_agt*", "vif", output_if);
      `uvm_info("top_tb", "use wildchar in top_tb's config_db::set!", UVM_LOW)
end
```
可以進一步簡化
```
initial begin
      uvm_config_db#(virtual my_if)::set(null, "*i_agt*", "vif", input_if);
      uvm_config_db#(virtual my_if)::set(null, "*o_agt*", "vif", output_if);
end
```
這種寫法極大簡化了程式碼，用起來非常方便。但是，並不建議使用通配符。通配符的存在使得原本非常清晰的設定路徑變得撲朔迷離。盡量避免使用通配符；即使要用，也盡可能不要過於「省略」。在如下的兩種方式中，第一種比第二種好很多：
```
uvm_config_db#(virtual my_if)::set(null, "uvm_test_top.env.i_agt*", "vif", input_if);
uvm_config_db#(virtual my_if)::set(null, "*i_agt*", "vif", input_if);
```
## check_config_usage
check_config_usage，它可以顯示截止到此函數呼叫時有哪些參數是被設定過但是卻沒有被獲取過。由於 config_db 的 set 及 get 語句一般都用於 build_phase 階段，所以此函數一般在 connect_phase 被呼叫：
```
virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        check_config_usage();
endfunction
```
PS: 也可以在 connect_phase 後的任一 phase 被呼叫
**Example**
config 設定
```
function void my_case0::build_phase(uvm_phase phase);
    …
    // 第一個是設定 default_sequence
    uvm_config_db#(uvm_object_wrapper)::set(this,
                                            "env.i_agt.sqr.main_phase",
                                            "default_sequence",
                                            case0_sequence::type_id::get());
    // 第二個是設定 driver 中 pre_num 的值，但不小心把 i_agt 寫成 i_atg
    uvm_config_db#(int)::set(this,
                             "env.i_atg.drv",
                             "pre_num",
                             999);
    // 第三個是設定 reference model 中 rm_value 的值
    uvm_config_db#(int)::set(this,
                             "env.mdl",
                             "rm_value",
                             10);
endfunction
```
在 my_driver 和 my_model 中分別取得 pre_num 和 rm_value 的值，這裡不列出相關程式碼。呼叫 check_config_usage 的運行結果是：
```
# UVM_INFO @ 0: uvm_test_top [CFGNRD] ::: The following resources have at least one write and no reads # default_sequence [/^uvm_test_top\.env\.i_agt\.sqr\.main_phase$/] : (class uvm_pkg::uvm_object_wrapper) # -
# --------
# uvm_test_top reads: 0 @ 0 writes: 1 @ 0
##
pre_num [/^uvm_test_top\.env\.i_atg\.drv$/] : (int) 999
# -
# --------
# uvm_test_top reads: 0 @ 0 writes: 1 @ 0
#
```
上述結果顯示有兩個設定資訊分別被寫過（set）1 次，但一次也沒有被讀取（get）。其中 pre_num 未被讀取是因為錯把 i_agt 寫成了 i_atg。 default sequence 的設定也沒有被讀取，是因為 default sequence 是設定給 main_phase 的，它在 main_phase 的時候被獲取，而 main_phase 是在 connect_phase 之後執行的。
## set_config 與 get_config
* set_config_int 與 uvm_config_db#（int）：：set 是完全等價的
* get_config_int 與 uvm_config_db#（int）：：get是完全等價的
* 除了 set/get_config_int 外，還有 set/get_config_string 和 set/get_config_object。它們分別對應uvm_config_db#（string）：：set/get和 uvm_config_db#（uvm_object）：：set/get
* config_db 比 set/get_config 強大的地方在於，它所設定的參數類型並不限於以上三種  
常見的枚舉類型、virtual interface、bit類型、佇列等都可以成為config_db設定的資料型別
## 命令列參數來對它們進行設置
```
<sim command> +uvm_set_config_int=<comp>,<field>,<value>
<sim command> +uvm_set_config_string=<comp>,<field>,<value>
```
```
<sim command> +uvm_set_config_int="uvm_test_top.env.i_agt.drv,pre_num,'h8" // 16 進位
```
