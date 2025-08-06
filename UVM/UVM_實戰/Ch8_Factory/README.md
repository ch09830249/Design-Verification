# UVM 中的 factory 機制
## 任務與函數的重載
當在父類別中定義一個函數/任務時，如果將其設置為 virtual 類型，那麼就可以在子類別中重載這個函數/任務：
```
class bird extends uvm_object;
  virtual function void hungry();        // 有 virtual
    $display("I am a bird, I am hungry");
  endfunction

  function void hungry2();               // 沒 virtual
    $display("I am a bird, I am hungry2");
  endfunction
endclass

class parrot extends bird;
  virtual function void hungry();
    $display("I am a parrot, I am hungry");
  endfunction

  function void hungry2();
    $display("I am a parrot, I am hungry2");
  endfunction
endclass
```
1. hungry 就是虛函數，它可以被重載。但是 hungry2 不是虛函數，不能被重載
2. 當指標以父類別的類型傳遞時，其表現出的行為依然是子類別的行為
```
function void my_case0::print_hungry(bird b_ptr);
  b_ptr.hungry();   // virtual => 支援多型，依物件實際型態呼叫
  b_ptr.hungry2();  // 非 virtual => 根據指標型別（這裡是 bird）呼叫
endfunction

function void my_case0::build_phase(uvm_phase phase);
  bird bird_inst;
  parrot parrot_inst;

  super.build_phase(phase);

  bird_inst = bird::type_id::create("bird_inst");
  parrot_inst = parrot::type_id::create("parrot_inst");

  print_hungry(bird_inst);    // 會呼叫 bird 的 hungry 和 hungry2
  print_hungry(parrot_inst);  // hungry 是 virtual，呼叫 parrot 的版本
                              // hungry2 非 virtual，仍會呼叫 bird 的版本
endfunction
```
如上所示的 print_hungry 函數，它能接收的函數型別是 bird。所以第一個呼叫時，對應 b_ptr 指向的實例是 bird 類型的，b_ptr 本身是 bird 類型的，所以顯示的是：
```
"I am a bird, I am hungry"
"I am a bird, I am hungry2"
```
```
"I am a parrot, I am hungry"
"I am a bird, I am hungry2"
```
在這個呼叫中，對應 b_ptr 指向的實例是 parrot 類型的，而 b_ptr 本身雖然是 parrot 類型的，但是在呼叫 hungry 函數時，它被隱式地轉換成了 bird 類型。 hungry 是虛函數，所以即使轉換成了 bird 類型，印出來的還是 parrot。但是 hungry2 不是虛函數，打印出來的就是 bird 了

這種函數/任務重載的功能在 UVM 中得到了大量的應用。其實最典型的莫過於各個 phase。當各個 phase 被呼叫時，以 build_phase 為例，實際上系統是使用如下的方式呼叫：
```
c_ptr.build_phase();
```
其中 c_ptr 是 uvm_component 類型的，而不是其他類型，如 my_driver（但是 c_ptr 指向的實例卻是 my_driver 類型的）。在一個驗在證平台中，UVM 樹上的結點是各個類型的，UVM 不必理會它們具體是什麼類型，統一將它們當作 uvm_component 來對待，這極大方便了管理。
## 約束的重載
在測試一個接收 MAC 功能的 DUT 時，有許多異常情況需要測試，例如 preamble 錯誤、sfd 錯誤、CRC 錯誤等。針對這些錯誤，在 transaction 中分別加入標誌位：
```
class my_transaction extends uvm_sequence_item;

  rand bit [47:0] dmac;
  rand bit [47:0] smac;
  rand bit [15:0] ether_type;
  rand byte pload[];
  rand bit [31:0] crc;

  rand bit crc_err;
  rand bit sfd_err;
  rand bit pre_err;
......
  `uvm_object_utils_begin(my_transaction)
    `uvm_field_int(dmac, UVM_ALL_ON)
    `uvm_field_int(smac, UVM_ALL_ON)
    `uvm_field_int(ether_type, UVM_ALL_ON)
    `uvm_field_array_int(pload, UVM_ALL_ON)
    `uvm_field_int(crc, UVM_ALL_ON)
    `uvm_field_int(crc_err, UVM_ALL_ON | UVM_NOPACK)
    `uvm_field_int(sfd_err, UVM_ALL_ON | UVM_NOPACK)
    `uvm_field_int(pre_err, UVM_ALL_ON | UVM_NOPACK)
  `uvm_object_utils_end
......
endclass
```
這些錯誤都是異常的情況，在大部分測試案例中，它們的值都應該為 0。所以 default constraint 是
```
constraint default_cons{
  crc_err dist{0 := 999_999_999, 1 := 1};
  pre_err dist{0 := 999_999_999, 1 := 1};
  sfd_err dist{0 := 999_999_999, 1 := 1};
}
```
在隨機化時，crc_err、pre_err 和 sfd_err 只有 1/1_000_000_000 的可能性取值為 1，其餘均為 0。但是其中最大的問題是其何時取 1、何時取 0 是無法控制的。如果某個測試案例用於測試正常的功能，裡面則不能有錯誤產生，換句話說，crc_err、pre_err 和 sfd_err 的值要一定為 0。上面的 constraint 顯然不能滿足，這種要求有 2 種解決方案。
1. 在定義 transaction 時，使用如下的方式定義 constraint：
```
class my_transaction extends uvm_sequence_item;
......
  constraint crc_err_cons {
    crc_err == 1'b0;
  }

  constraint sfd_err_cons {
    sfd_err == 1'b0;
  }

  constraint pre_err_cons {
    pre_err == 1'b0;
  }
......
endclass
```
在正常的測試案例中，可以使用以下方式隨機化：
```
my_transaction tr;
`uvm_do(tr)
```
在異常的測試案例中，可以使用以下方式隨機化：
```
virtual task body();
  m_trans = new();
  `uvm_info("sequence", "turn off constraint", UVM_MEDIUM)
  m_trans.crc_err_cons.constraint_mode(0);                        // 關閉名為 crc_err_cons 的 constraint，讓你能對 crc_err 做額外的隨機化控制
  m_trans.constraint_mode(0);                                     // 關掉所有 constraint
  // 這個巨集會自動 randomize 並將 transaction 傳送到 driver，適用於 sequence 中送出單一 transaction 的情境
  `uvm_rand_send_with(m_trans, {crc_err dist {0 := 2, 1 := 1};})  // 指定隨機分布，使 crc_err 有 2/3 的機率為 0，1/3 為 1
endtask
```
PS: 能夠使用這種方式的前提是 m_trans 已經被實例化。如果不實例化，直接使用 uvm_do 巨集：
```
my_transaction m_trans;
m_trans.crc_err_cons.constraint_mode(0);
`uvm_do(m_trans)
```
2. SystemVerilog 中一個非常有用的特性是支援約束的重載。因此，依然使用第一種方式中 my_transaction 的定義，在其基礎上派生一個新的 transaction：
```
class new_transaction extends my_transaction;
  `uvm_object_utils(new_transaction)

  function new(string name = "new_transaction");
    super.new(name);
  endfunction

  constraint crc_err_cons {
    crc_err dist {0 := 2, 1 := 1};
  }
endclass
```
在這個新的 transaction 中將 crc_err_cons 重載了。因此，在異常的測試案例中，可以使用如下的方式隨機化：
```
virtual task body();
  new_transaction ntr;

  repeat (10) begin
    `uvm_do(ntr)
    ntr.print();
  end
endtask
```
## factory 機制式的重載
以前面程式碼清單為例，定義好 bird 與 parrot，並在測試案例中呼叫 print_hungry 函數。將程式碼的 build_phase 中改為如下語句：
```
function void my_case0::build_phase(uvm_phase phase);
  set_type_override_by_type(bird::get_type(), parrot::get_type());  // 這行表示當建立 bird 類型時，實際會產生 parrot 類型的物件，這是 UVM 的 型別覆寫（type override） 機制。

  bird_inst   = bird::type_id::create("bird_inst");      // 雖然指定產生 bird，但因為有 type override，實際上會產生 parrot。
  parrot_inst = parrot::type_id::create("parrot_inst");  // 直接建立 parrot 物件。
  
  print_hungry(bird_inst);
  print_hungry(parrot_inst);
endfunction
```
```
"I am a parrot, I am hungry"
"I am a bird, I am hungry2"
"I am a parrot, I am hungry"
"I am a bird, I am hungry2"
```
雖然 print_hungry 接收的是 bird 類型的參數，但從運行結果可以推測出來，無論是第一次還是第二次呼叫 print_hungry，傳遞的都是類型為 bird 但是指向 parrot 的指標。對於第二次調用，可以很好理解，但第一次卻使人很難接受。這就是factory機制的重載功能。
<img width="1086" height="754" alt="image" src="https://github.com/user-attachments/assets/9d2f0531-19ed-464b-93e2-d16438ddcc51" />
<img width="1078" height="708" alt="image" src="https://github.com/user-attachments/assets/bd847f67-6c1b-4bb6-87b0-9e9201a57656" />
雖然 bird_inst 在實例化以及傳遞給 hungry 的過程中，沒有過與 parrot 的任何接觸，但它最終指向了一個 parrot 的實例。這是因 bird_inst 使用了 UVM 的 factory 機制式的實例化方式：
在實例化時，UVM 會透過 factory 機制在自己內部的一張表格中查看是否有相關的重載記錄。 set_type_override_by_type 語句相當於在 factory 機制的表格中加入了一筆記錄。當查到有重載記錄時，會使用新的類型來取代舊的類型。所以雖然在 build_phase 中寫明創建 bird 的實例，但最後卻建立了 parrot 的實例。
使用 factory 機制的重載是有前提的，並不是任意的類別都可以互相重載。要使用重載的功能，必須滿足以下要求：
**第一，無論是重載的類別（parrot）或被重載的類別（bird），都要在定義時註冊到factory機制中。**
**第二，被重載的類別（bird）在實例化時，要使用 factory 機制式的實例化方式，而不能使用傳統的 new 方式。**
**第三，最重要的是，重載的類別（parrot）要與被重載的類別（bird）有派生關係。重載的類別必須派生自被重載的類，被重載的類別必須是重載類別的父類別。**
**第四，component 與 object 之間互相不能重載。雖然 uvm_component 是派生自 uvm_object，但這兩者的血緣關係太遠了，遠到根本不能重載。從兩者的 new 參數的函數就可以看出來，二者互相重載時，多出來的一個 parent 參數會使 factory 機制無所適從。**
若沒有派生關係，會出現類似以下的 error messege
```
UVM_FATAL @ 0: reporter [FCTTYP] Factory did not return an object of type 'bird'.A component of type 'bear'
```
若有派生關係，但是順序顛倒了，即重載的類別是被重載類別的父類，那麼也會出錯
```
UVM_FATAL @ 0: reporter [FCTTYP] Factory did not return an object of type 'parrot'. A component of type
```
## 重載的方式及種類
上節介紹了使用 set_type_override_by_type 函數可以實作兩種不同類型之間的重載。這個函數位於 uvm_component 中，其原型是：
```
extern static function void set_type_override_by_type(uvm_object_wrapper original_type,
                                                      uvm_object_wrapper override_type,
                                                      bit replace=1);
```
這個函數有三個參數，其中第三個參數是 replace，將會在下節講述這個參數。實際應用上一般只用前兩個參數  
**第一個參數是被重載的類型，**  
**第二個參數是重載的類型。**  
但有時候可能並不是希望把驗證平台中的 A 類型全部替換成 B 類型，而只是替換其中的某一部分，這種情況就要用到 set_inst_override_by_type 函數。這個函數的原型如下：
```
extern function void set_inst_override_by_type(string relative_inst_path,
                                                uvm_object_wrapper original_type,
                                                uvm_object_wrapper override_type);
```
其中  
**第一個參數是相對路徑**，  
**第二個參數是被重載的類型，**  
**第三個參數是要重載的類型。**  
假設有以下的 new monitor 定義：
```
class new_monitor extends my_monitor;
    `uvm_component_utils(new_monitor)
    
    virtual task main_phase(uvm_phase phase);
    fork
      super.main_phase(phase);
    join_none
    `uvm_info("new_monitor", "I am new monitor", UVM_MEDIUM)
    endtask
endclass
```
以 UVM 樹為例
<img width="1095" height="781" alt="image" src="https://github.com/user-attachments/assets/bcc22967-9d7a-44a7-bd2e-4a643169171a" />
要將 env.o_agt.mon 替換成 new_monitor
```
set_inst_override_by_type("env.o_agt.mon", my_monitor::get_type(), new_monitor::get_type());
```
經過上述替換後，執行到 main_phase 時，會輸出下列語句：
```
I am new_monitor
```
無論是 set_type_override_by_type 或是 set_inst_override_by_type，它們的參數都是一個 uvm_object_wrapper 型的型別參數，這種
參數透過 xxx：：get_type() 的形式取得。 UVM 還提供了另外一種簡單的方法來替換這種晦澀的寫法：字串。
與 set_type_override_by_type 相對的是 set_type_override，它的原型是：
```
extern static function void set_type_override(string original_type_name,        // 透過 Class 的名稱
                                              string override_type_name,
                                              bit replace=1);
```
要使用 parrot 替換 bird，只需要加入下列語句：
```
set_type_override("bird", "parrot")
```
與 set_inst_override_by_type 相對的是 set_inst_override，它的原型是：
```
extern function void set_inst_override(string relative_inst_path,
                                        string original_type_name,
                                        string override_type_name);
```
對於上面使用 new_monitor 重載 my_monitor 的例子，可以使用以下語句：
```
set_inst_override("env.o_agt.mon", "my_driver", "new_monitor");
```
上述的所有函數都是 uvm_component 的函數，但是如果在一個無法使用 component 的地方，**如在 top_tb 的 initial 語句裡，就無法
使用。UVM 提供了另外四個函數來取代上述的四個函數，這四個函數的原型是：**
```
extern function
void set_type_override_by_type (uvm_object_wrapper original_type,
                                uvm_object_wrapper override_type,
                                bit replace=1);
extern function
void set_inst_override_by_type (uvm_object_wrapper original_type,
                                uvm_object_wrapper override_type,
                                string full_inst_path);
extern function
void set_type_override_by_name (string original_type_name,
                                string override_type_name,
                                bit replace=1);
extern function
void set_inst_override_by_name (string original_type_name,
                                string override_type_name,
                                string full_inst_path);
```
這四個函數都位於 uvm_factory 類別中，其中  
第一個函數與 uvm_component 中的同名函數類似，傳遞的參數相同。
第二個對應 uvm_component 中的同名函數，只是其輸入參數變了，這裡需要輸入一個字串類型的 full_inst_path。這個 full_inst_path 就是要替換的實例中使用 get_full_name() 得到的路徑值。  
第三個與 uvm_component 中的 set_type_override 類似，傳遞的參數相同。
第四個函數字對應 uvm_component 中的 set_inst_override，也需要一個 full_inst_path。  
如何使用這四個函數呢？**系統中存在一個 uvm_factory 類型的全域變數 factory**可以在 initial 語句裡使用如下的方式呼叫這四個
函數：
```
initial begin
    factory.set_type_override_by_type(bird::get_type(), parrot::get_type());
end
```
在一個 component 內也完全可以直接呼叫 factory 機制的重載函數：
```
factory.set_type_override_by_type(bird::get_type(), parrot::get_type());
```
事實上，uvm_component 的四個重載函數直接呼叫了 factory 的對應函數。
除了可以在程式碼中進行重載外，還可以在**命令列中進行重載**。對於實例重載和類型重載，分別有各自的命令列參數：
```
<sim command> +uvm_set_inst_override=<req_type>,<override_type>,<full_inst_path>
<sim command> +uvm_set_type_override=<req_type>,<override_type>[,<replace>]
```
這兩個命令列參數分別對應於 set_inst_override_by_name 和 set_type_override_by_name。對於實例重載：
```
<sim command> +uvm_set_inst_override="my_monitor,new_monitor,uvm_test_top.env.o_agt.mon"
```
對於類型重載：
```
<sim command> +uvm_set_type_override="my_monitor,new_monitor"
```
類型重載的命令列參數中有三個選項，其中最後一個 replace 表示是否可以被後面的重載覆蓋。
## 複雜的重載
事實上，UVM 支援連續的重載。還是以 bird 與 parrot 的例子來敘述，現在從 parrot 又派生出了一個新的類別 big_parrot：
```
class big_parrot extends parrot;
  virtual function void hungry();
    $display("I am a big_parrot, I am hungry");
  endfunction

  function void hungry2();
    $display("I am a big_parrot, I am hungry2");
  endfunction

  `uvm_object_utils(big_parrot)

  function new(string name = "big_parrot");
    super.new(name);
  endfunction
endclass
```
在 build_phase 中設定如下的連續重載，並呼叫 print_hungry 函數：
```
function void my_case0::build_phase(uvm_phase phase);
  bird bird_inst;
  parrot parrot_inst;
  super.build_phase(phase);

  set_type_override_by_type(bird::get_type(), parrot::get_type());          // bird       => parrot
  set_type_override_by_type(parrot::get_type(), big_parrot::get_type());    // parrot     => big parrot

  bird_inst = bird::type_id::create("bird_inst");
  parrot_inst = parrot::type_id::create("parrot_inst");
  print_hungry(bird_inst);
  print_hungry(parrot_inst);
endfunction
```
最後輸出是 (bird => parrot => big parrot)
```
# I am a big_parrot, I am hungry      // print_hungry(bird_inst);
# I am a bird, I am hungry2
# I am a big_parrot, I am hungry      // print_hungry(parrot_inst);
# I am a bird, I am hungry2
```
除了這種連續的重載外，還有一種是替換式的重載。假如從 bird 派生出了新的鳥 sparrow：
```
class sparrow extends bird;
  virtual function void hungry();
    $display("I am a sparrow, I am hungry");
  endfunction

  function void hungry2();
    $display("I am a sparrow, I am hungry2");
  endfunction

  `uvm_object_utils(sparrow)

  function new(string name = "sparrow");
    super.new(name);
  endfunction
endclass
```
在 build_phase 中設定如下重載：
```
function void my_case0::build_phase(uvm_phase phase);
  bird bird_inst;
  parrot parrot_inst;
  super.build_phase(phase);

  set_type_override_by_type(bird::get_type(), parrot::get_type());      // bird    =>  parrot
  set_type_override_by_type(bird::get_type(), sparrow::get_type());     // bird    =>  sparrow

  bird_inst = bird::type_id::create("bird_inst");
  parrot_inst = parrot::type_id::create("parrot_inst");
  print_hungry(bird_inst);
  print_hungry(parrot_inst);
endfunction
```
最後輸出
```
# I am a sparrow, I am hungry      // 最終是 sparrow
# I am a bird, I am hungry2
# I am a parrot, I am hungry       // parrot 沒有替換紀錄
# I am a bird, I am hungry2
```
在建立 bird 的實例時，**factory 機制會查詢到兩個相關的記錄**，它並不會在看完第一筆記錄後即直接建立一個 parrot 的實例，而是
最後看完第二筆記錄後才會建立 sparrow 的實例。由於是讀取完最後的語句後才可以建立實例，所以其實下列的重載方式也是允
許的：
```
function void my_case0::build_phase(uvm_phase phase);
  bird bird_inst;
  super.build_phase(phase);

  set_type_override_by_type(bird::get_type(), parrot::get_type());              // bird    => parrot  (A)
  set_type_override_by_type(parrot::get_type(), sparrow::get_type(), 0);        // parrot  => sparrow (B)    sparrow extend from bird not parrot

  bird_inst = bird::type_id::create("bird_inst");
  print_hungry(bird_inst);
endfunction
```
最後輸出
```
# I am a sparrow, I am hungry
# I am a bird, I am hungry2
```
在上述 A 的重載語句與 B 的重載四前提中的第三條相違背，sparrow 並沒有派生自 parrot，但是依
然可以重載 parrot。但這樣使用依然是有條件的，最終創建出的實例是 sparrow 類型的，而最初是 bird 類型的，這兩者之間仍然有
派生關係。程式碼清單8-38與程式碼清單8-37相比，去掉了對 parrot_inst 的實例化。因為在程式碼清單8-38中第86行存在的情況下，再實
例化一個 parrot_inst 會出錯。所以，8.2.1節中的重載四前提的第三條應該改為：
**在有多個重載時，最終重載的類別要與最初被重載的類別有派生關係。最終重載的類別必須派生自最初被重載的類，最初被重載的
類別必須是最終重載類別的父類別**
## factory 機制的調試
factory 機制的重載功能很強大，UVM 提供了 print_override_info 函數來輸出所有的列印訊息，以上節中的 new_monitor 重載 
my_monitor 為例：
```
set_inst_override_by_type("env.o_agt.mon", my_monitor::get_type(), new_monito r::get_type());
```
## print_override_info
驗證平台中僅有這一句重載語句，那麼呼叫 print_override_info 函數列印的方式為：
```
function void my_case0::connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      env.o_agt.mon.print_override_info("my_monitor");
endfunction
```
最終輸出的資訊為：
```
# Given a request for an object of type 'my_monitor' with an instance
# path of 'uvm_test_top.env.o_agt.mon', the factory encountered
# the following relevant overrides. An 'x' next to a match indicates a
# match that was ignored.
##
Original Type Instance Path Override Type
# ------------- -------------------------- -------------
# my_monitor uvm_test_top.env.o_agt.mon new_monitor            // 這裡會明確列出原始類型和新類型
##
Result:
##
The factory will produce an object of type 'new_monitor'
```
在呼叫 print_override_info 時，其輸入的類型應該是原始的類型，而不是新的類型。
print_override_info 是一個 uvm_component 的成員函數，它實質上是呼叫 uvm_factory 的 debug_create_by_name。
## debug_create_by_type
除了這個函數外，uvm_factory 還有 debug_create_by_type，其原型為：
```
extern function void debug_create_by_type (uvm_object_wrapper requested_type,
                                            string parent_inst_path="",
                                            string name="");
```
使用它對 new_monitor 進行調試的程式碼為：
```
factory.debug_create_by_type(my_monitor::get_type(), "uvm_test_top.env.o_agt.mon");
```
其輸出與使用 print_override_info 相同。
## print
除了上述兩個函數外，uvm_factory 也提供 print 函數：
```
extern function void print (int all_types=1);
```
這個函數只有一個參數，其取值可能為 0、1 或 2。當為 0 時，僅列印被重載的實例和類型，其列印出的資訊大致如下：
```
#### Factory Configuration (*)
##
Instance Overrides:
##
Requested Type Override Path Override Type
# -------------- -------------------------- -------------
# my_monitor uvm_test_top.env.o_agt.mon new_monitor
#
# No type overrides are registered with this factory
```
當為 1 時，列印參數為 0 時的信息，以及所有使用者建立的、註冊到 factory 的類別的名稱。
當為 2 時，列印參數為 1 時的信息，以及系統所建立的、所有註冊到 factory 的類別的名稱（如 uvm_reg_item）。
## print_topology
除了上述這些函數外，還有另外一個重要的工具可以顯示出整棵 UVM 樹的拓樸結構，這個工具就是 uvm_root 的 print_topology
函數。 UVM 樹在 build_phase 執行完成後才完全建立完成，因此，這個函數應該在 build_phase 之後呼叫：
```
uvm_top.print_topology();
```
最終顯示的結果（部分）為：
```
--------------------------------------------------------------------
Name Type Size Value
--------------------------------------------------------------------
<unnamed> uvm_root - @158
uvm_test_top my_case0 - @455
env my_env - @469
…
i_agt my_agent - @481
…
mon my_monitor - @822
…
o_agt my_agent - @489
mon new_monitor - @865
…
```
從這個拓樸結構中可以清楚看出，env.o_agt.mon 被重載成了 new_monitor 類型。 print_topology 這個函數非常有用，即使在不
進行 factory 機制偵錯的情況下，也可以透過呼叫它來顯示整個驗證平台的拓樸結構是否與自己預期的一致。因此可以把其放在所
有測試用例的基底類別 base_test 中。
## 常用的重載
## 重載 transaction
在有了 factory 機制的重載功能後，建置 CRC 錯誤的測試案例就多了一種選擇。假設有如下的正常 sequence，此 sequence 被作為
某個測試用例的 default_sequence：
```
// normal case (不會有 CRC error)
class normal_sequence extends uvm_sequence #(my_transaction);
......
  virtual task body();
    repeat (10) begin
      `uvm_do(m_trans)
    end
    #100;
  endtask
......
  `uvm_object_utils(normal_sequence)
endclass
```
這裡的 my_transaction 使用8.1.2節程式碼清單8-7的定義。現在要建立一個新的測試案例，這是一個異常的測試案例，要測試 
CRC 錯誤的情況。可以從這個 transaction 派生一個新的 transaction：
```
// 派生出 crc err 的 transaction
class crc_err_tr extends my_transaction;
......
  // 重載 my_transaction 的 constraint
  constraint crc_err_cons{
    crc_err == 1;
  }
endclass
```
如果使用8.1.2節程式碼清單8-13的方法，那麼需要新建一個 sequence，然後將這個 sequence 作為新的測試案例的
default_sequence：
```
class abnormal_sequence extends uvm_sequence #(my_transaction);
  crc_err_tr tr;
  virtual task body();
      repeat(10) begin
          `uvm_do(tr)
      end
  endtask
endclass
function void my_case0::build_phase(uvm_phase phase);
…
  uvm_config_db#(uvm_object_wrapper)::set(this,
                                          "env.i_agt.sqr.main_phase",
                                          "default_sequence",
                                          abnormal_sequence::type_id::get());
endfunction
```
但有了 factory 機制的重載功能後，可以不用重寫一個 abnormal_sequence，而繼續使用 normal_sequence 作為新的測試案例
的 default_sequence，只需要將 my_transaction 使用 crc_err_tr 重載：
```
function void my_case0::build_phase(uvm_phase phase);
  super.build_phase(phase);

  factory.set_type_override_by_type(my_transaction::get_type(), crc_err_tr::get_type());    // my_transaction    =>    crc_err_tr
  // 這裡 default sequence 還是 normal_sequence
  uvm_config_db#(uvm_object_wrapper)::set(this,
                                          "env.i_agt.sqr.main_phase",
                                          "default_sequence",
                                          normal_sequence::type_id::get());
endfunction
```
經過這樣的重載後，normal_sequence 產生的 transaction 就是 CRC 錯誤的 transaction。這比新建一個 CRC 錯誤的 sequence 的方式簡
練了很多。
## 重載 sequence
transaction 可以重載，同樣的，sequence 也可以重載。上節使用的 transaction 重載能工作的前提是約束也可以重載。但是很多人
可能並不習慣於這種用法，而習慣於最原始的如8.1.2節中代碼清單8-9的方法。
在其他測試案例中已經定義瞭如下的兩個 sequence：
```
class normal_sequence extends uvm_sequence #(my_transaction);

  virtual task body();
    `uvm_do(m_trans)
    m_trans.print();
  endtask

  `uvm_object_utils(normal_sequence)
endclass

class case_sequence extends uvm_sequence #(my_transaction);

  virtual task body();
    normal_sequence nseq;
    repeat(10) begin
      `uvm_do(nseq)
    end
  endtask

endclass
```
這裡使用了巢狀的 sequence。 case_sequence 被當作 default_sequence。現在新建一個測試用例時，可以仍然將 case_sequence 作為 
default_sequence，只需要從 normal_sequence 派生一個例外的 sequence：
```
class abnormal_sequence extends normal_sequence;
......
  virtual task body();
    m_trans = new("m_trans");
    m_trans.crc_err_cons.constraint_mode(0);
    `uvm_rand_send_with(m_trans, {crc_err == 1;})
    m_trans.print();
  endtask
endclass
```
並且在 build_phase 中將 normal_sequence 使用 abnormal_sequence 重載掉：
```
function void my_case0::build_phase(uvm_phase phase);
  factory.set_type_override_by_type(normal_sequence::get_type(), abnormal_sequence::get_type());
  uvm_config_db#(uvm_object_wrapper)::set(this,
                                          "env.i_agt.sqr.main_phase",
                                          "default_sequence",
                                          case_sequence::type_id::get());
endfunction
```
本節所述的內容其實與上節的類似，都能達到同樣的目的。這就是UVM的強大之處，對於同樣的事情，它提供多種方式完
成，使用者可以自由選擇。
## 重載 component
8.3.1節和8.3.2節分別使用重載 transaction 和重載 sequence 的方式產生異常的測試案例。其實，還可以使用重載 driver 的方式產
生。假設某個測試案例使用8.3.1節程式碼清單8-45的 normal_sequence 作為其 default_sequence。這是一個只產生正常 transaction 的 
sequence，使用它建構的測試案例是一個正常的用例。現在如果要產生一個 CRC 錯誤的測試案例，可以依然使用這個 sequence 作為
default_sequence，只是需要定義如下的 driver：
```
class crc_driver extends my_driver;
......
  virtual function void inject_crc_err(my_transaction tr);
    tr.crc = $urandom_range(10000000, 0);
  endfunction

  virtual task main_phase(uvm_phase phase);
    vif.data <= 8'b0;
    vif.valid <= 1'b0;
    while(!vif.rst_n)
      @(posedge vif.clk);
    while(1) begin
      seq_item_port.get_next_item(req);
      inject_crc_err(req);
      drive_one_pkt(req);
      seq_item_port.item_done();
    end
  endtask

endclass
```
然後在 build phase 中將 my_driver 使用 crc_driver 重載：
```
function void my_case0::build_phase(uvm_phase phase);
  factory.set_type_override_by_type(my_driver::get_type(), crc_driver::get_type());
  uvm_config_db#(uvm_object_wrapper)::set(this,
                                          "env.i_agt.sqr.main_phase",
                                          "default_sequence",
                                          normal_sequence::type_id::get());
endfunction
```
在本節所舉的例子中看不出重載driver的優勢，因為CRC錯誤是一個非常普通的異常測試案例。對於那些特別異常的測試用
例，異常到使用sequence實現起來非常麻煩的情況，重載driver就會顯示出其優勢。
除了driver可以重載外，scoreboard與參考模型等都可以重載。尤其對於參考模型來說，處理異常的激勵源是相當耗時的一件
事情。可能對於一個DUT來說，其80%的程式碼都是用來處理異常情況，作為模擬DUT的參考模型來說，更是如此。如果將所有的
異常情況都用一個參考模型實現，那麼這個參考模型程式碼量將會非常大。但是如果將其分散為數十個參考模型，則每一個處理一種
異常情況，當建立相應異常的測試案例時，將正常的參考模型由它替換掉。這樣，可使程式碼清晰，並增加了可讀性。
## 重載 driver 以實現所有的測試案例
重載driver使得一些在sequence中比較難實現的測試案例輕易地在driver中實作。那如果放棄sequence，只使用factory機制實
現測試用例可能嗎？答案確實是可能的。當不用sequence時，那麼要在driver中控制發送包的種類、數量，對於objection的控制又
要從sequence回到driver中，恰如2.2.3節那樣，似乎一切都回到了起點。
但不推薦這麼做：
·引入sequence的原因是將資料流產生的功能從driver中獨立出來。取消sequence相當於一種倒退，會使得driver的功能不明
的確，與現代程式設計中模組化、功能化的趨勢不合。
·雖然用driver實作某些測試案例比sequence更方便，但是對於另外一些測試案例，在sequence裡做起來會比driver中更加方
便。
·sequence的強大之處在於，它可以在一個sequence中啟動另外的sequence，從而可以最大程度地實現不同測試用例之間
sequence的重用。但是對於driver來說，要實現這樣的功能，只能將一些基本的產生激勵的函數寫在基類driver中。用戶會發現到最
後這個driver的程式碼量非常恐怖。
·使用virtual sequence可以協調、同步不同激勵的產生。當放棄sequence時，在不同的driver之間完成這樣的同步則比較難。
基於以上原因，請不要將所有的測試案例都使用driver重載實作。只有將driver的重載與sequence結合，才與UVM的最初設
計初衷相符合，也才能建構起可重用性高的驗證平台。完成同樣的事情有很多種方式，應綜合考慮選擇最合理的方式。

