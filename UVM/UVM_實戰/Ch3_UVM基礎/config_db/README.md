# UVM 中的路徑
* 一個 component（如 my_driver）內透過 get_full_name（）函式可以得到此 component 的路徑
```
function void my_driver::build_phase();
  super.build_phase(phase);
  $display("%s", get_full_name());
endfunction
```
ch2 的層次結構中的 my_driver 中，那麼印出來的值就是 uvm_test_top.env.i_agt.drv  
![image](https://github.com/user-attachments/assets/a8020746-ef76-41de-b702-40e1ac0e4aa4)
* uvm_test_top 實例化時的名字是 uvm_test_top，這個名字是由 UVM 在 run_test 時自動指定的
* uvm_top 的名字是 __top__，但是在顯示路徑的時候，並不會顯示出這個名字，而只顯示從 uvm_test_top 開始的路徑
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
uvm_config_db#(int)::get(null, "uvm_test_top.env.i_agt.drv", "pre_num_max", p re_num_max);
```
* **get 函數**
  * 一般的，如果第一個參數被設定為 this，那麼第二個參數可以是一個空的字串
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
  `uvm_info("my_driver", $sformatf("before super.build_phase, the pre_num is %0d", pre_num), UVM_LOW)
  super.build_phase(phase);
  `uvm_info("my_driver", $sformatf("after super.build_phase, the pre_num is %0d", pre_num), UVM_LOW)
  if(!uvm_config_db#(virtual my_if)::get(this, "", "vif", vif))
    `uvm_fatal("my_driver", "virtual interface must be set for vif!!!")
endfunction
```
* **只要使用 uvm_field_int 註冊，並且在 build_phase 中呼叫 super.build_phase（），就可以省略在 build_phase 中的 get 語句**
  uvm_config_db#(int)::get(this, "", "pre_num", pre_num);
* 這裡的關鍵是 build_phase 中的 super.build_phase 語句，當執行到 driver 的 super.build_phase 時，會自動執行 get 語句。
  * 第一，my_driver 必須使用 uvm_component_utils 巨集註冊
  * 第二，pre_num 必須使用 uvm_field_int 巨集註冊
  * 第三，在呼叫 set 函數的時候，set 函數的第三個參數必須與要 get 函數中變數的名字一致，也就是必須是 pre_num
    * 所以上節中，雖然說這兩個參數可以不一致，但是**最好的情況還是一致**
      李四的信是給李四的，不要打什麼暗語，用一個「四」來代替李四
* **對於 set 語句，則沒有辦法省略**
## 跨層次的多重設置
在前面的所有例子中，都是設定一次，取得一次。但是假如設定多次，只取得一次，最後會得到哪個數值呢？
在現實生活中，這可以理解成有好多人都給李四發了一封信，要求李四做某件事情，但是這些信是相互矛盾的。那麼李四有
兩種方法來決定聽誰的：一是以收到的時間為準，最近收到的信具有最高的權威，當同時收到兩封信時，則看發信人的權威性，
也即時間的優先順序最高，發信人的優先順序次之；二是先看發信人，哪個發信人最權威就聽誰的，當同一個發信人先後發了兩封信
時，那麼最近收到的一封權威高，也就是發信人的優先順序最高，而時間的優先順序低。 UVM中採用類似第二種方法的機制。
在圖3-4中，假如uvm_test_top和env中都對driver的pre_num的值進行了設置，在uvm_test_top中的設置語句如下：
