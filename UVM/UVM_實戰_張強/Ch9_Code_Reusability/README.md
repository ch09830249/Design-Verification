# UVM 中程式碼的可重複使用性
## 廣義的 callback 函數
在前文介紹 my_transaction 時，曾經在其 post_randomize 中呼叫 calc_crc 函式：
```
function void post_randomize();
  crc = calc_crc;
endfunction
```
my_transaction 的最後一個欄位是 CRC 校驗資訊。假如沒有 post_randomize()，那麼 **CRC 必須在整個 transaction 的資料都固定之後才能計算出來**。
```
my_transaction tr;
assert(tr.randomize());
tr.crc = tr.calc_crc();
```
執行前兩句之後，tr 中的 crc 欄位的值是一個隨機的值，要將其設定成真正反映這個 transaction 資料的 CRC 訊息，需要在 randoimize() 之後呼叫一個 calc_crc，calc_crc 是一個自訂的函數。
因為每次執行 randomize 函數之後都要調用一次，如果忘記調用，將很可能成為驗證平台的一個隱患，非常隱蔽且不容易發現。期望有一種方法能夠在執行 randomize 函數之後自動呼叫 calc_crc 函數。randomize 是 SystemVerilog 提
供的一個函數，同時 SystemVerilog 也提供了一個 post_randomize() 函數，當 randomize() 之後，系統會自動呼叫 post_randomize 
函數，像如上的三句話，執行時實際如下：
```
my_transaction tr;
assert(tr.randomize());
tr.post_randomize();
tr.crc=tr.calc_crc();
```
其中 tr.post_randomize 是自動呼叫的，所以如果能夠重載 post_randomize 函數，在其中執行 calc_crc 函數，那麼就可以達到目的
了：
```
function void my_transaction::post_randomize();
  super.post_randomize();
  crc=this.calc_crc();
endfunction
```
post_randomize 就是 SystemVerilog 提供的一個 callback 函數。這也是最簡單的 callback 函數。
引言中強調兩個項目之間。不過如果將 SystemVerilog 語言的開發過程作為一個專案 A，驗證人員使用 SystemVerilog 開發的是專案 B。 A 的開發者預料到 B 可能會在 randomize 函數完成後做一些事情，於是 A 為 SystemVerilog 加入了 post_randomize 函數。 B 如 A 所料，使用了這個 callback 函數。
post_randomize 函數是 SystemVerilog 提供的廣義的 callback 函數。 UVM 也為使用者提供了廣義的 callback 函數/任務：pre_body 和
 post_body，除此之外還有 pre_do、mid_do 和 post_do。相信很多用戶已經從中受益了。
## UVM 中 callback 機制的原理
對於 VIP（Verification Intellectual Property）來說，一個很容易預測的需求是在 driver 中，**在發送 transaction 之前，使用者可能會
針對 transaction 做某些動作，因此應該提供一個 pre_tran 的接口**，如用戶 A 可能在 pre_tran 中將要發送內容的最後 4 個字節設置為發送
的包的序號，這樣在包出現比對錯誤時，可以快速地定位，B 用戶可能在整個包發送之前先在線路上發送幾個特殊的字節，C 用戶
可能將整個包的長度截去一部分，D 用戶…
總之不同的用戶會有不同的需求。正是 callback 機制的存在，滿足了這種需求，擴大了 VIP 的應用範圍。
```
task my_driver::main_phase();
  …
  while(1) begin
    seq_item_port.get_next_item(req);
    pre_tran(req);
    …
  end
endtask
```
假設這是一個成熟的 VIP 中的 driver，那麼考慮如何實作 pre_tran 的 callback 函數/任務呢？它應該是 my_driver 的函數/任務。
如果按照上面 post_randomize 的經驗，那麼應該從 my_driver 衍生一個類別 new_driver，然後重寫 pre_tran 這個函數/任務。但這種想法
是行不通的，因為這是一個完整的 VIP，雖然從 my_driver 派生了 new_driver，但是這個 VIP 中正常運行時使用的依然是 my_driver，
而不是 new_driver。new_driver 這個衍生類別根本就沒有實例化過，所以 pre_tran 從來不會運作。為了解決這個問題，嘗試**新引入一個類別**：
```
task my_driver::main_phase();
…
  while(1) begin
    seq_item_port.get_next_item(req);
    A.pre_tran(req);
  …
  end
endtask
```
這樣可以避免重新定義一次 my_driver，**只需要重新定義 A 的 pre_tran 即可**。重新派生 A 的代價是要遠小於 my_driver 的。
在使用的時候，只要從 A 派生一個類別並將其實例化，然後重新定義其 pre_tran 函數，此時 callback 機制的目的就達到了。雖然看
起來似乎一切順利，但實際上卻忽略了一點。因為從 A 派生了一個類，並且實例化，但是作為 my_driver 來說，怎麼知道 A 派生了一個類
呢？又怎麼知道 A 實例化了呢？為了應付這個問題，UVM 中又引入了一個類，假設這個類稱為 A_pool，意思是專門存放 A 或 A 
的派生類別的一個池子。 UVM 約定會執行這個池子中所有實例的 pre_tran 函數/任務，即：
```
task my_driver::main_phase();
…
  while(1) begin
    seq_item_port.get_next_item(req);
    foreach(A_pool[i]) begin
      A_pool[i].pre_tran(req);
    end
  …
  end
endtask
```
這樣，在使用的時候，只要從 A 派生一個類別並將其實例化，然後加入到 A_pool 中，那麼系統運行到上面的 foreach(A_pool[i])
語句時，將會知道加入了一個實例，於是就會呼叫其 pre_tran 函數 (任務)。
有了 A 和 A_pool，真正的 callback 機制就可以實現了。UVM 中的 callback 機制與此類似，不過其程式碼實作非常複雜。
# callback 機制的使用
要實現真正的 pre_tran，需要先定義上節所說的類 A：
```
文件：src/ch9/section9.1/9.1.4/callbacks.sv
class A extends uvm_callback;
  virtual task pre_tran(my_driver drv, ref my_transaction tr);
  endtask
endclass
```
A 類一定要從 uvm_callback 派生，另外還需要定義一個 pre_tran 的任務，此任務的型別一定要是 virtual 的，因為從 A 派生的類需
要重載這個任務。
接下來聲明一個 A_pool 類別：
```
文件：src/ch9/section9.1/9.1.4/callbacks.sv
typedef uvm_callbacks#(my_driver, A) A_pool;
```
A_pool 的宣告相當簡單，只需要一個 typedef 語句。另外，在這個聲明中除了要**指明這是一個 A 類型的池子外，還要指明
這個池子將會被哪個類別使用**。在本例中，my_driver 將會使用這個池子，所以要將此池子宣告為 my_driver 專用的。之後，在 
my_driver 中要做如下聲明：
```
文件：src/ch9/section9.1/9.1.4/my_driver.sv
typedef class A;

class my_driver extends uvm_driver#(my_transaction);
  …
  `uvm_component_utils(my_driver)
  /* 註冊 callback,
    參數1: 使用 callback 的 component
    參數2: 欲使用 callback 的 base class (PS: 記得要註冊其 base class)
  */
  `uvm_register_cb(my_driver, A)  
  …
endclass
```
這個聲明與 A_pool 的類似，要指明 my_driver 和 A。在 my_driver 的 main_phase 中呼叫 pre_tran 時並不如上節所示的那麼簡單，而
是呼叫了一個巨集來實作：
```
文件：src/ch9/section9.1/9.1.4/my_driver.sv
task my_driver::main_phase(uvm_phase phase);
…
  while(1) begin
    seq_item_port.get_next_item(req);
    `uvm_do_callbacks(my_driver, A, pre_tran(this, req))
    drive_one_pkt(req);
    seq_item_port.item_done();
  end
endtask
```
uvm_do_callbacks 巨集的第一個參數是呼叫 pre_tran 的類別的名字，這裡自然是 my_driver，第二個參數是哪個類別具有pre_tran，這裡
是A，第三個參數是呼叫的是函數/任務，這裡是pre_tran，在指明是pre_tran時，要順便給出pre_tran的參數。
到目前為止是VIP的開發者應該要做的事情，作為使用VIP的使用者來說，需要做以下事情：
首先從 A 派生一個類別：
```
class my_callback extends A;
  virtual task pre_tran(my_driver drv, ref my_transaction tr);
  `uvm_info("my_callback", "this is pre_tran task", UVM_MEDIUM)
  endtask
  
  `uvm_object_utils(my_callback)
endclass
```
其次，在測試案例中將 my_callback 實例化，並將其加入 A_pool：
```
function void my_case0::connect_phase(uvm_phase phase);
  my_callback my_cb;
  super.connect_phase(phase);
  
  my_cb = my_callback::type_id::create("my_cb");
  A_pool::add(env.i_agt.drv, my_cb);
endfunction
```
my_callback 的實例化是在 connect_phase 中完成的，實例化完成後需要將 my_cb 加入 A_pool。同時，在加入時需要指定是給
哪個 my_driver 使用的。因為很可能整個 base_test 中實例化了多個 my_env，從而有多個 my_driver 的實例，所以要將 my_driver 的路徑
作為 add 函數的第一個參數。
至此，一個簡單的 callback 機制範例就完成了。這個範例幾乎涵蓋 UVM 中所有可能用到的 callback 機制的知識，大部分 callback
機制的使用都與這個例子相似。
總結一下，對於 VIP 的開發者來說，預留一個 callback 函數/任務介面時需要做以下幾步：
* 定義一個 A 類
* 聲明一個 A_pool 類
* 在要預留 callback 函數/任務介面的類別中呼叫 uvm_register_cb 宏
* 在要呼叫 callback 函數/任務介面的函數/任務中，使用 uvm_do_callbacks 宏
對於 VIP 的使用者來說，需要做以下幾步：
* 從 A 派生一個類，在這個類別中定義好 pre_tran
* 在測試案例的 connect_phase（或其他 phase，但一定要在程式碼清單9-11使用此callback函數/任務的phase之前）將從 A 派
生的類別實例化，並加入A_pool中，如程式清單9-13所示。
本節的 my_driver 是自己寫的，my_case0 也是自己寫的。完全不存在 VIP 與 VIP 使用者的情況。不過換個角度來說，可能有兩個
驗證人員共同開發一個項目，一個負責建構測試平台（testbench）及 my_driver 等的程式碼，另外一位負責建立測試案例。負責搭建
測試平台的驗證人員為建立測試案例的人員留下了callback函數/任務介面。即使my_driver與測試案例都由同一個人來寫，也是完
全可以接受的。因為不同的測試案例肯定會引起不同的driver的行為。這些不同的行為差異可以在sequence中實現，也可以在driver
中實現。在driver中實作時既可以用driver的factory機制重載，也可以使用本節所講的callback機制。 9.1.6節將探討只使用callback機
制來搭建所有測試案例的可能。
