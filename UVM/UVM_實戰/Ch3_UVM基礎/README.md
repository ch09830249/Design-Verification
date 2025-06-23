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
