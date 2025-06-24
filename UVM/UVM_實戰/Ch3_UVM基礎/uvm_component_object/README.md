# uvm_component 派生自 uvm_object
1. uvm_component 擁有 uvm_object 的特性，同時又有自己的一些特質，但 uvm_component 的一些特性，uvm_object 則不一定有
2. uvm_component 有兩大特性是 uvm_object 所沒有的
    1. 透過在 new 的時候指定 parent 參數來形成一種樹形的組織結構
    2. 有 phase 的自動執行特點
![image](https://github.com/user-attachments/assets/386be6d9-686e-4a92-9ed9-5c7d480f7ab1)  
PS: 最左邊分支的類別或直接衍生自 uvm_object 的類，是不可能以結點的形式出現在 UVM 樹上的。
# 常用的派生自 uvm_object 的类
1. 除了派生自 uvm_component 類別以外的類，幾乎所有的類別都衍生自 uvm_object
2. 在驗證平台中常遇到的派生自 uvm_object 的類別有：
    * **uvm_sequence_item**
      * 讀者定義的所有的 **transaction 要從 uvm_sequence_item 派生**  
        transaction 就是封裝了一定資訊的一個類，本書中的 my_transaction 就是將一個 mac 幀中的各個字段封裝在了一起，  
        包括目的地址、來源地址、幀類型、幀的資料、FCS校驗和等
      * driver 從 sequencer 中得到 transaction，並且把其轉換成連接埠上的訊號
        **PS: 不能從 uvm_transaction 派生一個 transaction，而要從 uvm_sequence_item 派生**
    * **uvm_sequence**
      * **所有的 sequence 要從 uvm_sequence 派生一個**
      * sequence 就是 sequence_item 的組合
      * sequence 直接與 sequencer 打交道，當 driver 向 sequencer 索取資料時，sequencer 會檢查是否有 sequence 要傳送資料。當發現有 sequence_item 待發送時，會將此 sequence_item 交給 driver
    * **config**
      * 所有的 config 一般都直接從 uvm_object 派生
      * config 的主要功能就是規格驗證平台的行為  
        如規定 driver 在讀取總線時地址訊號要持續幾個時鐘，片選訊號從什麼時候開始有效等
      * **使用 config_db 進行參數配置，這裡的 config 其實指的是把所有的參數放在一個 object 中，然後透過 config_db 的方式設定給所有需要這些參數的 component**
    * **uvm_reg_item (後續介紹)**
      * 它衍生自 uvm_sequence_item，用於 register model 中
      * uvm_reg_map、uvm_mem、uvm_reg_field、uvm_reg、uvm_reg_file、uvm_reg_block 等與暫存器相關的眾多的類別都是衍生自
uvm_object，它們都是用於 register model
    * **uvm_phase**
      * 它派生自 uvm_object，其主要作用為控制 uvm_component 的行為方式，使得 uvm_component 平滑地在各個不同的 phase 之間依序運轉
# 常用的派生自uvm_component的類
與 uvm_object 相比，派生自 uvm_component 的類比較少
* **uvm_driver**
    * 所有的 driver 都要派生自 uvm_driver
    * driver 的功能主要就是向 sequencer 索取 sequence_item（transaction），並且將 sequence_item 裡的資訊驅動到 DUT 的連接埠上，這相當於完成了從 transaction 等級到 DUT 能夠接受的連接埠層級資訊的轉換。
* **uvm_monitor**
    * 所有的 monitor 都要派生自 uvm_monitor
    * monitor 是從 DUT 的 pin 上接收數據，並且把接收到的數據轉換成 transaction 級別的 sequence_item，再把轉換後的數據發送給 
scoreboard，供其比較
    * 雖然從理論上來說所有的 monitor 要從 uvm_monitor派生。但實際上如果從 uvm_component派生，也沒有任何問題
* **uvm_sequencer**
    * 所有的 sequencer 都要派生自 uvm_sequencer
    * sequencer 的功能就是組織管理 sequence，當 driver 要求資料時，它就把 sequence 產生的 sequence_item 轉發給 driver
    * 與 uvm_component 相比，uvm_sequencer 做了相當多的擴展，具體的會在第6章中介紹
* **uvm_scoreboard**
    * 一般的 scoreboard 都要派生自 uvm_scoreboard
    * scoreboard 的功能就是比較 reference model 和 monitor 分別發送來的數據，根據比較結果判斷 DUT 是否正確運作
* **reference model**
    * UVM 中並沒有針對 reference model 定義一個類別。所以通常來說，reference model都是直接衍生自 uvm_component。
    * reference model 的作用就是模仿 DUT，完成與 DUT 相同的功能。DUT 是用 Verilog 寫成的時序電路，而 reference
model 則可以直接使用 SystemVerilog 高階語言的特性，同時也可以透過 DPI 等介面呼叫其他語言來完成與 DUT 相同的功能。
* **uvm_agent**
    * 所有的 agent 要派生自 uvm_agent
    * 與前面幾個比起來，uvm_agent 的作用並不是那麼明顯。它只是把 driver 和 monitor 封裝在一起，根據參數值來決定只實例化 monitor還是要同時實例化 driver 和 monitor
    * agent 的使用主要是從可重複使用的角度來考慮的。如果在做驗證平台時不考慮可重複使用性，那麼 agent 其實是可有可無的。
    * uvm_agent 的最大改動在於引入了一個變數 is_active
```
virtual class uvm_agent extends uvm_component;
    uvm_active_passive_enum is_active = UVM_ACTIVE;
...
    function void build_phase(uvm_phase phase);
      int active;
      super.build_phase(phase);
      if(get_config_int("is_active", active)) 
        is_active = uvm_active_passive_enum'(active);
    endfunction
```
PS: get_config_int 是 uvm_config_db#（int）：：get 的另一種寫法，這種寫法最初出現在 OVM 中，本書將在3.5.9節詳細地講述這種
寫法。由於 is_active 是一個枚舉變量，其兩個取值為固定值0或1。所以在上面的程式碼中可以以 int 型別傳遞給 uvm_agent，並針對傳遞過來的資料做強制型別轉換。
* **uvm_env**
    * 所有的env（environment的縮寫）要派生自uvm_env
    * env 將驗證平台上用到的固定不變的 component 都封裝在一起。這樣，當要執行不同的測試案例時，只要在測試案例中實例化此 env 即可
* **uvm_test**
    * 所有的測試用例要派生自 uvm_test 或其派生類，**不同的測試用例之間差異很大，所以從 uvm_test 派生出來的類別各不相同**
    * 任何一個派生出的測試案例中，都要實例化 env，只有這樣，當測試用例在運行的時候，才能把資料正常地發給 DUT，並正常地接收 DUT 的資料
# 與 uvm_object 相關的巨集
* **uvm_object_utils**
    * 它用來把一個直接或間接派生自 uvm_object 的類別註冊到 factory 中
* **uvm_object_param_utils**
    * 它用來把一個直接或間接派生自 uvm_object 的**參數化的類別註冊到 factory 中**。所謂參數化的類，是指類似於如下的類別：
      EX: class A#(int WIDTH=32) extends uvm_object;
* **uvm_object_utils_begin**
    * 當需要使用 field_automation 機制時，就需要使用此巨集
* **uvm_object_param_utils_begin**
    * 與 uvm_object_utils_begin 宏一樣，只是它適用於參數化的且其中某些成員變數要使用 field_automation 機制實作的類別
* **uvm_object_utils_end**
    * 它總是與 uvm_object_*_begin 成對出現，作為 factory 註冊的結束標誌
# 與 uvm_component 相關的宏
* **uvm_component_utils**
    * 它用來把一個直接或間接派生自 uvm_component 的類別註冊到 factory 中
* **uvm_component_param_utils**
    * 它用來把一個直接或間接派生自 uvm_component 的參數化的類別註冊到 factory 中
* **uvm_component_utils_begin**
    * 這個巨集與 uvm_object_utils_begin 相似，它用於同時需要使用 factory 機制和 field_automation 機制註冊的類
    * 在類似 my_transaction 這種類別中使用 field_automation 機制可以讓人理解，可是在 component 中使用 field_automation 機制有必要嗎？
        * uvm_component 派生自 uvm_object，所以對於 object 擁有的如 compare、print 函數都可以直接使用  
          但是 filed_automation 機制對於 uvm_component 來說最大的意義不在於此，而是可以自動地使用 config_db 來得到某些變數的值 (後續介紹)
* **uvm_component_param_utils_begin**
    * 與 uvm_component_utils_begin 宏一樣，只是它適用於參數化的，且其中某些成員變數要使用 field_automation 機制實作的類別
* **uvm_component_utils_end**
    * 它總是與 uvm_component_*_begin 成對出現，作為 factory 註冊的結束標誌
# uvm_component 的限制
uvm_component 是從 uvm_object 派生來的。從理論上來說，uvm_component 應該具有 uvm_object 的所有的行為特徵。但是，由於 uvm_component 是作為 UVM 樹的結點存在的，這一特性使得它**失去了 uvm_object 的某些特徵**。
* 在 uvm_object 中有 **clone 函數，它用來分配一塊記憶體空間，並把另一個實例複製到這塊新的記憶體空間**。  
clone 函數的使用方式如下：
```
class A extends uvm_object;
…
endclass
class my_env extends uvm_env;
    virtual function void build_phase(uvm_phase phase);
        A a1;
        A a2;
        a1 = new("a1");
        a1.data = 8'h9;
        $cast(a2, a1.clone());
    endfunction
endclass
```
**上述的 clone 函數無法用於 uvm_component 中，因為一旦使用後，新 clone 出來的類，其 parent 參數無法指定。**
* **copy 函數也是 uvm_object 的一個函數，在使用 copy 前，目標實例必須已經使用new函數分配好了記憶體空間**，而使用 clone 函數時，目標實例可以只是一個空指標。換言之，**clone = new + copy**。
* **雖然uvm_component無法使用clone函數，但可以使用copy函數** 因為在呼叫 copy 之前，目標實例已經完成了實例化，其 parent 參數已經指定了。
* uvm_component 的另一個限制是，**位於同一個父結點下的不同的 component，在實例化時不能使用相同的名字**
