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
如上所示的 print_hungry 函數，它能接收的函數型別是 bird。所以第一個呼叫時，對應 b_ptr 指向的實例是 bird 類型的，b_ptr 本身是bird類型的，所以顯示的是：
```
"I am a bird, I am hungry"
"I am a bird, I am hungry2"
```
```
"I am a parrot, I am hungry"
"I am a bird, I am hungry2"
```
在這個呼叫中，對應 b_ptr 指向的實例是 parrot 類型的，而 b_ptr 本身雖然是 parrot 類型的，但是在呼叫 hungry 函數時，它被隱式地轉換成了 bird 類型。 hungry 是虛函數，所以即使轉換成了 bird 類型，印出來的還是 parrot。但是 hungry2 不是虛函數，打
印出來的就是 bird 了

這種函數/任務重載的功能在 UVM 中得到了大量的應用。其實最典型的莫過於各個 phase。當各個 phase 被呼叫時，以 build_phase 為例，實際上系統是使用如下的方式呼叫：
```
c_ptr.build_phase();
```
其中 c_ptr 是 uvm_component 類型的，而不是其他類型，如 my_driver（但是 c_ptr 指向的實例卻是 my_driver 類型的）。在一個驗在證平台中，UVM 樹上的結點是各個類型的，UVM 不必理會它們具體是什麼類型，統一將它們當作 uvm_component 來對待，這極大方便了管理。
