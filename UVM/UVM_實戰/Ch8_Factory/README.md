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
extern static function void set_type_override(string original_type_name,
                                              string override_type_name,
                                              bit replace=1);
```
