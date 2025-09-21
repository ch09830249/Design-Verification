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
總結一下，
* 對於 **VIP 的開發者**來說，預留一個 callback 函數/任務介面時需要做以下幾步：
  * 定義一個 A 類
  * 聲明一個 A_pool 類
  * 在要預留 callback 函數/任務介面的類別中呼叫 uvm_register_cb 宏
  * 在要呼叫 callback 函數/任務介面的函數/任務中，使用 uvm_do_callbacks 宏
* 對於 **VIP 的使用者來說**，需要做以下幾步：
  * 從 A 派生一個類，在這個類別中定義好 pre_tran
  * 在測試案例的 connect_phase（或其他 phase，但一定要在程式碼清單9-11使用此callback函數/任務的phase之前）將從 A 派生的類別實例化，並加入 A_pool 中

本節的 my_driver 是自己寫的，my_case0 也是自己寫的。完全不存在 VIP 與 VIP 使用者的情況。不過換個角度來說，可能有兩個
驗證人員共同開發一個項目，一個負責建構測試平台（testbench）及 my_driver 等的程式碼，另外一位負責建立測試案例。負責搭建
測試平台的驗證人員為建立測試案例的人員留下了callback函數/任務介面。即使my_driver與測試案例都由同一個人來寫，也是完
全可以接受的。因為不同的測試案例肯定會引起不同的driver的行為。這些不同的行為差異可以在sequence中實現，也可以在driver
中實現。在driver中實作時既可以用driver的factory機制重載，也可以使用本節所講的callback機制。 9.1.6節將探討只使用callback機
制來搭建所有測試案例的可能。
## 子類別繼承父類別的 callback 機制
考慮如下一種情況，某公司有前後兩代產品。其中第一代產品已經成熟，有一個已經建置好的驗證平台，現在要在此基礎上
開發第二代產品，需要建造一個新的驗證平台。這個新的驗證平台大部分與舊的驗證平台一致，只是需要擴充 my_driver 的功能，
即需要從原來的 driver 中派生一個新的類別 new_driver。另外，需要確保第一代產品的所有測試案例在盡量不改動的前提下能在新的
驗證平台上通過。在第一代產品的測試案例中，大量使用了 callback 機制。由於一個 callback 池（即 A_pool）在聲明的時候指明了這個池子只能裝載用於 my_driver 的 callback。那麼怎樣才能使原來的 callback 函數/任務能夠用於 new_driver 中呢？
這就牽扯到了子類別繼承父類別的 callback 函數/任務問題。 my_driver 使用上節中的定義，在此基礎上派生新的類別 new_driver：
```
class new_driver extends my_driver;
  `uvm_component_utils(new_driver)
  `uvm_set_super_type(new_driver, my_driver)
…
endclass

task new_driver::main_phase(uvm_phase phase);
…
  while(1) begin
    seq_item_port.get_next_item(req);
    `uvm_info("new_driver", "this is new driver", UVM_MEDIUM)
    `uvm_do_callbacks(my_driver, A, pre_tran(this, req))
    drive_one_pkt(req);
    seq_item_port.item_done();
  end
endtask
```
這裡使用了 **uvm_set_super_type 宏，它把子類別和父類別關聯在一起**。其第一個參數是子類，第二個參數是父類。在 main_phase 中
當呼叫 uvm_do_callbacks 巨集時，其第一個參數是 my_driver，而不是 new_driver，即呼叫方式與在 my_driver 中一樣。
在 my_agent 中實例化此 new_driver：
```
function void my_agent::build_phase(uvm_phase phase);
  super.build_phase(phase);
  if (is_active == UVM_ACTIVE) begin
    sqr = my_sequencer::type_id::create("sqr", this);
    drv = new_driver::type_id::create("drv", this);
  end
  mon = my_monitor::type_id::create("mon", this);
endfunction
```
這樣，上節的 my_case0 不用經過任何修改就可以在新的驗證平台上通過。
## 使用 callback 函數/任務來實現所有的測試案例
可以在 pre_tran 中做很多事情，那麼是否可以將 driver 中的 drive_one_pkt 也移到 pre_tran 中呢？答案是可以
的。更進一步，將 seq_item_port.get_nex_item 移到 pre_tran 中也是可以的。
其實完全可以不用 sequence，只用 callback 函數/任務就可以實現所有的測試案例。假設 A 類定義如下：
```
class A extends uvm_callback;
  my_transaction tr;

  virtual function bit gen_tran();
  endfunction

  virtual task run(my_driver drv, uvm_phase phase);
    phase.raise_objection(drv);

    drv.vif.data <= 8'b0;
    drv.vif.valid <= 1'b0;
    while(!drv.vif.rst_n)
      @(posedge drv.vif.clk);

    while(gen_tran()) begin
      drv.drive_one_pkt(tr);
    end
    phase.drop_objection(drv);
  endtask
endclass
```
在 my_driver 的 main_phase 中，去掉所有其他程式碼，只呼叫 A 的 run：
```
task my_driver::main_phase(uvm_phase phase);
  `uvm_do_callbacks(my_driver, A, run(this, phase))
endtask
```
在建立新的測試案例時，只需要從 A 派生一個類，並重載其 gen_tran 函數：
```
class my_callback extends A;
  int pkt_num = 0;

  virtual function bit gen_tran();
    `uvm_info("my_callback", "gen_tran", UVM_MEDIUM)
    if(pkt_num < 10) begin
      tr = new("tr");
      assert(tr.randomize());
      pkt_num++;
      return 1;
    end
    else
      return 0;
  endfunction

  `uvm_object_utils(my_callback)
endclass
```
在這種情況下，新測試案例相當於重載 gen_tran。如果不符合要求，也可以將 A 類的 run 任務重載
在這個範例中完全丟棄了 sequence 機制，在 A 類別的 run 任務中進行控制 objection，激勵產生在 gen_tran 中
## callback 機制、sequence 機制與 factory 機制
上一節使用 callback 函數/任務實現所有的測試案例，幾乎完全顛覆了這本書從頭到尾一直在強調的 sequence 機制。在8.3.4節也
見識到了使用 factory 機制重載 driver 來實現所有測試用例的情況。
callback 機制、sequence 機制和 factory 機制在某種程度上來說很像：它們都能實現建構測試案例的目的。只是 sequence 機制是
 UVM 一直提倡的生成激勵的方式，UVM 為此做了大量的工作，例如構建了許多宏、嵌套的 sequence、virtual sequence、可重用性
等。
8.3.4節所列的四個理由，依然適用於 callback 機制。雖然 callback 機制能夠實現所有的測試用例，但是某些測試用例用
 sequence 來實作則更加方便。 virtual sequence 的協調功能在 callback 機制中就很難實現。
callback 機制、sequence 機制和 factory 機制並不是互斥的，三者都能分別實現同一目的。當這三者互相結合時，又會產生許多
新的解決問題的方式。如果在建立驗證平台和測試案例時，能夠擇優選擇其中最簡單的一種實作方式，那麼建立出來的驗證平台
一定是夠強、夠簡練的。實現相同事情有多種方式，為用戶提供了多種選擇，高擴展性是 UVM 成功的一個重要原因。
## 小而美與 factory 機制的重載
factory 機制重要的一點是提供重載功能。一般來說，如果要用 B 類重載 A 類，那麼 B 類是要衍生自 A 類的。在派生時，要保留 A 
類別的大部分程式碼，只改變其中一小部分。
假設原始 A_driver 的 drive_one_pkt 任務如下：
```
task A_driver::drive_one_pkt;
  drive_preamble();
  drive_sfd();
  drive_data();
endtask
```
上述程式碼將一個 drive_one_pkt 任務又分成了三個子任務。現在如果要建構一個 sfd 錯誤的例子，那麼只需要從 A_driver 派生一個 
B_driver，並且重載其 drive_sfd 任務即可。
如果上述程式碼不是分成三個子任務，而是一個完整的任務：
```
task A_driver::drive_one_pkt;
  //drive preamble
  …
  //drive sfd
  …
  //drive data
  …
endtask
```
那麼在 B_driver 中需要重載的是 drive_one_pkt 這個任務：
```
task B_driver::drive_one_pkt;
  //drive preamble
  …
  //drive new sfd
  …
  //drive data
  …
endtask
```
此時，drive preamble 和 drive data 部分程式碼需要複製到新的 drive_one_pkt。對於程式設計師來說，要盡量避免複製的使用：
* 在複製中由於不小心，很容易出現各種各樣的錯誤。雖然這些錯誤只是短期的，馬上就能修訂，但畢竟要為此花費額外的時間
* 從長遠來看，如果 drive data 相關的程式碼稍微有一點變動，此時 A_driver 和 B_driver 的 drive_one_pkt 都需要修改，這又需要額外
花費時間。同樣的程式碼只在驗證平台上出現一處，如果要重複使用，將它們封裝成可重載的函數/任務或類別。
## 放棄建造強大 sequence 的想法
UVM 的 sequence 功能非常強大，許多用戶喜歡將他們的 sequence 寫得非常完美，他們的目的是建造通用的 sequence，有些用戶
甚至執著於一個 sequence 解決驗證平台中所有的問題，在使用時，只需要設定參數即可。
以一個 my_sequence 為例，有些使用者可能希望這個 sequence 有下列功能：
* 能夠產生正常的乙太網路包
* 透過設定參數產生CRC錯誤的包
* 透過設定參數產生sfd錯誤的包
* 透過設定參數產生preamble錯誤的套件
* 透過設定參數產生CRC與sfd同時錯誤的包
* 透過設定參數產生CRC與preamble同時錯誤的包
* 透過設定參數產生sfd與preamble同時錯誤的套件
* 透過設定參數產生CRC、sfd與preamble同時錯誤的包
* 透過配置參數控制錯誤的機率
* 透過設定參數選擇要傳送的資料是隨機化的還是從檔案讀取
* 透過設定參數選擇如果從文件讀取，那麼是多文件還是單文件
* 透過設定參數選擇如果從檔案讀取，那麼使用哪一種檔案格式
* 透過設定參數選擇是否將發送出去的套件寫入檔案中
* 透過設定參數選擇長包、中包、短包各自的閾值長度
* 透過設定參數選擇長包、中包、短包的發送比例
* 透過設定參數選擇是否在套件的負載中加入目前要傳送的套件的序號，以便於偵錯
……
上述 sequence 確實是一個非常通用、強悍的 sequence。但是這個 sequence 有兩個問題：
第一，這個 **sequence 的程式碼量非常大，分支眾多，後期維護相當麻煩**。如果程式碼編寫者與維護者不是同一個人，那麼對於維
護者來說，簡直就是災難。即使程式碼編寫者與維護者是同一個人，那麼在一段時間之後，自己也可能被自己以前寫的東西感到迷
惑不已。  
第二，**使用這個 sequence 的人面對這麼多的參數，他要如何選擇呢**？他有時只想使用其中最基本的功能，但卻不知道
怎麼配置，只能所有的參數都看一遍。如果看一遍能看懂還好，但有時候即使看兩三次也看不懂。
如果用戶非常堅持上述超強大 的sequence，那麼請一定要​​做到以下兩點之一：
* 有一份完整的文檔介紹它
* 有較多的程式碼註釋

文件的重視程度因各公司而異，目前國內外的 IC 公司對於驗證文件重視的普遍不夠，很少有公司會為一個 sequence 建立專
門的文檔。當程式碼完成後，很少會有程式碼編寫者願意再寫文件。即使公司製度規定必須寫，文檔的品質也有高低之分，且存在文
檔的後期維護問題。當 sequence 建立後，為其建了一個文檔，但是後來 sequence 升級，文檔卻沒有升級。文檔與程式碼不一致，這也
是目前 IC 公司經常存在的問題。
程式碼的註解則與程式碼編寫者的編碼習慣有關。就目前來說，只有少數編碼習慣好的人能夠做到品質較好的註解。驗證人員編
寫的程式碼通常比較靈活，而且更新頻率較快。當設計變更時，相關的驗證程式碼就要變更。很多驗證人員並沒有寫註解的習慣，即
使有寫註釋，但是當後來代碼變更時，註釋可能已經落伍了。
因此，還是強烈建議不要使用強大的 sequence。可以將一個強大的 sequence 拆分成小的 sequence，如：
* normal_sequence
* crc_err_sequence
* rd_from_txt_sequence
……
盡量做到一看名字就知道這個 sequence 的用處，這樣可以最大程度上方便自己，方便大家。
## 參數化類別的必要性
程式碼的重用分為很多層次。凡是在某個專案中開發的程式碼用於其他項目，都可以稱為重用，如：
* A用戶在項目P中的代碼被A用戶自己用於項目P
* A用戶在專案P中的程式碼被A用戶自己用於專案Q
* A用戶在專案P中的程式碼被B用戶用於專案Q
* A用戶在專案P中開發的程式碼被B用戶或更多的用戶用於專案P或專案Q
以上四種應用場景對程式碼可重複使用性的要求逐漸提高。在第一種中，可能只是幾個sequence被幾個不同的測試案例使用；在最
後者中，可能A用戶開發的是一個匯流排功能模型，大家都會重複使用這些程式碼。
為了增加程式碼的可重複使用性，參數化的類別是一個很好的選擇。 UVM中廣泛使用了參數化的類別。對使用者來說，使用最多的參數化
的類別莫過於uvm_sequence了，其原型為：
```
virtual class uvm_sequence #(type REQ = uvm_sequence_item, type RSP = REQ) extends uvm_sequence_base;
```
在派生 uvm_sequence 時指定參數的類型，即 transaction 的類型，可以方便地產生 transaction 並建立測試案例。除了 
uvm_sequence 外，還有 uvm_analysis_port 等，不再一一列舉。
相較於普通的類，參數化的類別在定義時會有些複雜，其古怪的語法可能會使人望而卻步。並不是說所有的類別一定要定義成參數
化的類。對很多類來說，根本沒有參數可言，如果定義成參數化的類，根本沒有任何優勢可言。所以，定義成參數化的類別的前
提是，這個參數是有意義的、可行的。 2.3.1節的my_transaction是沒有任何必要定義成一個參數化的類別的。相反，一條總線
transaction（如7.1.1節的bus_transaction）可能需要定義成參數化的類，因為總線位寬可能是16位的、32位的或64位的。
