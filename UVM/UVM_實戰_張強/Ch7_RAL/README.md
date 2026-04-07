# 寄存器模型簡介
## 暫存器模型簡介
* **帶暫存器配置匯流排的 DUT**
先前所有的例子中，所使用的 DUT 幾乎都只有一組資料輸入輸出口，而沒有行為控制口，這樣的 DUT 幾乎是沒有任何價值的。通常來說，**DUT 中會有一組控制端口，透過控制端口，可以配置 DUT 中的暫存器，DUT 可以根據暫存器的值來改變其行為**。這組控制埠就是**暫存器配置匯流排**。如附錄 B 的程式碼清單 B-2 所示。  
```
module dut(clk, rst_n, bus_cmd_valid, bus_op, bus_addr, bus_wr_data, bus_rd_data, rxd, rx_dv, txd, tx_en);
    input clk;
    input rst_n;
    input bus_cmd_valid;
    input bus_op;
    input [15:0] bus_addr;
    input [15:0] bus_wr_data;
    output [15:0] bus_rd_data;
    input [7:0] rxd;
    input rx_dv;
    output [7:0] txd;
    output tx_en;

    reg[7:0] txd;
    reg tx_en;
    reg invert;

    always @(posedge clk) begin
        if(!rst_n) begin
            txd <= 8'b0;
            tx_en <= 1'b0;
        end
        else if(invert) begin
            txd <= ~rxd;     // 輸出時會將輸入的資料取反
            tx_en <= rx_dv;
        end
        else begin
            txd <= rxd;
            tx_en <= rx_dv;
        end
    end

    always @(posedge clk) begin
        if(!rst_n)
            invert <= 1'b0;
        else if(bus_cmd_valid && bus_op) begin
            case(bus_addr)
                16'h9: begin
                    invert <= bus_wr_data[0];
                end
                default: begin
                end
            endcase
        end
    end

    reg [15:0] bus_rd_data;
    always @(posedge clk) begin
        if(!rst_n)
            bus_rd_data <= 16'b0;
        else if(bus_cmd_valid && !bus_op) begin
            case(bus_addr)
                16'h9: begin
                    bus_rd_data <= {15'b0, invert};
                end
                default: begin
                    bus_rd_data <= 16'b0;
                end
            endcase
        end
    end

endmodule
```  
1. 在這個 DUT 中，只有一個 1 bit 的暫存器 invert，為其分配位址 16’h9  
    如果它的值為 1，那麼 DUT 在輸出時會將輸入的資料取反  
    如果為 0，則將輸入資料直接發送出去
2. invert 可以透過總線 bus_* 進行配置  
    bus_op 為 1 時表示**寫**操作  
    bus_op 為 0 表示**讀取**操作  
3. bus_addr 表示位址，bus_rd_data 表示**讀取的數據**，bus_wr_data 表示要**寫入的數據**
4. bus_cmd_valid 為 1 時表示總線數據有效，只持續一個時鐘，DUT 應該在其為 1 期間採樣總線數據  
    如果是讀取操作，應該在下一個時鐘給出讀取數據  
    如果是寫入操作，應該在下一個時脈把資料寫入  
    當在此總線上對 16‘h9（即 invert 暫存器）的位址進行讀寫操作時，會得到結果，對其他地址進行操作則不會有任何結果  
6. 不支援 burst 操作，不支援延遲回應等
  
針對此總線，有以下的transaction定義：  
src/ch7/section7.1/7.1.1/bus_transaction.sv  
```  
typedef enum {BUS_RD, BUS_WR} bus_op_e;

class bus_transaction extends uvm_sequence_item;

  rand bit[15:0] rd_data;
  rand bit[15:0] wr_data;
  rand bit[15:0] addr;

  rand bus_op_e bus_op;

  `uvm_object_utils_begin(bus_transaction)
    `uvm_field_int(rd_data, UVM_ALL_ON)
    `uvm_field_int(wr_data, UVM_ALL_ON)
    `uvm_field_int(addr,    UVM_ALL_ON)
    `uvm_field_enum(bus_op_e, bus_op, UVM_ALL_ON)
  `uvm_object_utils_end

  function new(string name = "bus_transaction");
    super.new(name);
  endfunction

endclass
```  

有如下的 driver 定義:  
src/ch7/section7.1/7.1.1/bus_driver.sv
```  
task bus_driver::run_phase(uvm_phase phase);
…
  while(1) begin
    seq_item_port.get_next_item(req);
    drive_one_pkt(req);
    seq_item_port.item_done();
  end
endtask

task bus_driver::drive_one_pkt(bus_transaction tr);
  `uvm_info("bus_driver", "begin to drive one pkt", UVM_LOW);
  repeat(1) @(posedge vif.clk);

  vif.bus_cmd_valid <= 1'b1;
  vif.bus_op <= ((tr.bus_op == BUS_RD) ? 0 : 1);
  vif.bus_addr <= tr.addr;
  vif.bus_wr_data <= ((tr.bus_op == BUS_RD) ? 0 : tr.wr_data);

  @(posedge vif.clk);
  vif.bus_cmd_valid <= 1'b0;
  vif.bus_op <= 1'b0;
  vif.bus_addr <= 16'b0;
  vif.bus_wr_data <= 16'b0;

  @(posedge vif.clk);
  if(tr.bus_op == BUS_RD) begin
    tr.rd_data = vif.bus_rd_data;
  end

  `uvm_info("bus_driver", "end drive one pkt", UVM_LOW);
endtask
```
需要說明的是，如果是讀取操作，這裡直接將讀到的資料賦值給 rd_data。  
在 sequence 中，可以使用以下方式**進行讀取操作**：  
src/ch7/section7.1/7.1.1/my_case0.sv
```  
virtual task body();
  `uvm_do_with(m_trans, {m_trans.addr == 16'h9;
                         m_trans.bus_op == BUS_RD;})
  `uvm_info("case0_bus_seq", $sformatf("invert's initial value is %0h", m_trans.rd_data), UVM_LOW)
endtask
```  
這裡用到了 6.7.3 節介紹的另類的 response，在 sequence 中直接引用 m_trans.rd_data 可以得到讀取資料的值。  
  
以如下的方式**進行寫入操作**：
src/ch7/section7.1/7.1.1/my_case0.sv
```  
virtual task body();
  `uvm_do_with(m_trans, {m_trans.addr == 16'h9;
                         m_trans.bus_op == BUS_WR;
                         m_trans.wr_data == 16'h1;})
endtask
```  
現在，整個驗證平台的框圖變成如圖 7-1 所示的形式。
<img width="1148" height="812" alt="image" src="https://github.com/user-attachments/assets/45d0f449-afdb-4864-a727-e1b974d0ce7c" />  
* **需要寄存器模型才能做的事情**  
考慮下一個問題，在上節所示的 DUT 中，invert 暫存器用於控制 DUT 是否將輸入的激勵位元取反。在取反的情況下，參考模型 (Reference Model) 需要讀取此暫存器的值，如果為 1，那麼其輸出 transaction 也需要進行反轉。可是如何在參考模型中讀取一個暫存器的值呢？就目前讀者所掌握的知識來說，**只能先透過使用 bus_driver 向總線上發送讀取指令，並給出要讀的暫存器位址來查看一個暫存器的值。** 要實現這個過程，需要啟動一個 sequence，這個 sequence 會發送一個 transaction 給 bus_driver。所以  
* 第一個問題是**如何在參考模型的控制下來啟動一個 sequence 以讀取暫存器**  
    **A:** 一個簡單的想法是設定一個**全域事件（又是全域變數！）**，然後在參考模型中觸發這個事件。在 virtual sequence 中等待這個事件的到來，等到了，則啟動 sequence。這裡用到了全域變量，這是相當忌諱的。如果不使用全域變量，那麼可以用一個非全域事件來取代。利用 config 機制分別為 virtual sequencer 和 scoreboard 設定一個 config_object，在此 object 中設定一個事件，例如 rd_reg_event，然後在 scoreboard 中觸發這個事件，而在 virtual sequence 中則要等待這個事件的到來：(這個事件等到後就啟動一個 sequence，開始讀取暫存器)
```  
@p_sequencer.config_object.rd_reg_event;
```
* 第二個問題是，**sequence 讀取的暫存器的值如何傳遞給參考模型**  
  **A:** 當 sequence 讀取到暫存器後，可以再透過 6.6.2 節所示的 config_db 傳遞給參考模型，在**參考模型中使用 6.6.3 節所示的 wait_modified 來更新資料**。  
  
從上面可以看出這個過程相當麻煩。在一個大的設計中，其暫存器有數百上千個。為了區分這麼多的暫存器，又需要許多其他額外的設定。其實，這個讀取過程可以使用寄存器模型來實作。如果有了寄存器模型，那麼這個過程就可以簡化為：
```
task my_model::main_phase(uvm_phase phase);
…
  reg_model.INVERT_REG.read(status, value, UVM_FRONTDOOR);
…
endtask
```  
只要一條語句就可以實現上述複雜的過程。像是啟動 sequence 及將讀取結果回傳這些事情，都會由暫存器模型來自動完成。如下圖顯示了讀取暫存器的過程，其中左圖為不使用暫存器模型，右圖為使用暫存器模型的讀取方式
<img width="1182" height="770" alt="image" src="https://github.com/user-attachments/assets/7278cf97-fc0d-4cf5-822b-d8641380e1ca" />  
* **在沒有暫存器模型之前**
  只能啟動 sequence 透過前門（FRONTDOOR）存取的方式來讀取暫存器，局限較大，在 scoreboard（或其他 component）中難以控制
* **有了暫存器模型之後**
  scoreboard 只與暫存器模型打交道，無論是**發送讀取的指令**還是**取得讀取操作的回傳值**，都可以由暫存器模型完成。有了暫存器模型後，**可以在任何耗費時間的 phase 中使用暫存器模型以前閘存取或後門（BACKDOOR）存取的方式來讀取暫存器的值**，同時還能在**某些不耗費時間的 phase（如check_phase）中使用後門訪問的方式來讀取暫存器的值**
* 前門存取與後門存取
    * 前門訪問: 指的是透過模擬 cpu 在總線上發出讀取指令，進行讀寫操作。在這個過程中，模擬時間（$time函數得到的時間）是一直往前走的
    * 後門訪問: 與前門訪問相對的概念。它不是透過總線進行讀寫操作，而是直接透過層次化的引用來改變暫存器的值
另外，暫存器模型也提供一些任務，如 mirror、update，它們可以批次完成暫存器模型與 DUT 中相關暫存器的交互作用。
可見，UVM 暫存器模型的本質就是重新定義了驗證平台與 DUT 的暫存器接口，使驗證人員能更好地組織及配置暫存器，簡化流程、減少工作量。
* **暫存器模型中的基本概念**
    * uvm_reg_field：這是暫存器模型中的最小單位。什麼是 reg_field？ 假如有一個狀態暫存器，它各位的意義如下圖所示  
<img width="1207" height="399" alt="image" src="https://github.com/user-attachments/assets/b46beebf-0fd3-47fd-805f-31bcae70db56" />  
如上的狀態暫存器共有四個域，分別是 empty、full、overflow、underflow。這四個域對應暫存器模型中的 uvm_reg_field。名字為「reserved」的並不是一個域
    * uvm_reg：它比uvm_reg_field 高一個級別，但還是比較小的單位。一個暫存器中至少包含一個 uvm_reg_field
    * uvm_reg_block：它是一個比較大的單位，在其中可以加入許多的 uvm_reg，也可以加入其他的 uvm_reg_block。一個寄存器模型中至少包含一個 uvm_reg_block
    * uvm_reg_map：每個暫存器在加入暫存器模型時都有其位址，**uvm_reg_map 就是儲存這些位址，並將其轉換成可以存取的物理位址**（**因為加入暫存器模型中的暫存器位址一般都是偏移位址，而不是絕對位址**）。當暫存器模型使用前門存取方式來實作讀取或寫入操作時，uvm_reg_map 就會將位址轉換成絕對位址，啟動一個讀取或寫入的 sequence，並將讀取或寫入的結果傳回。在每個 reg_block 內部，至少有一個（通常也只有一個）uvm_reg_map。
## 簡單的暫存器模型
* **只有一個暫存器的暫存器模型**
本節為 7.1.1 節所示的 DUT 建立暫存器模型。這個 DUT 非常簡單，它只有一個暫存器 invert。要為其建造寄存器模型，首先要從 uvm_reg 派生一個 invert 類別：
src/ch7/section7.2/reg_model.sv
```  
class reg_invert extends uvm_reg;

  rand uvm_reg_field reg_data;

  virtual function void build();
    reg_data = uvm_reg_field::type_id::create("reg_data");
    // parameter: parent, size, lsb_pos, access, volatile, reset value, has_reset, is_rand, individually accessible
    reg_data.configure(this, 1, 0, "RW", 1, 0, 1, 1, 0);
  endfunction

  `uvm_object_utils(reg_invert)

  function new(input string name="reg_invert");
    // parameter: name, size, has_coverage
    super.new(name, 16, UVM_NO_COVERAGE);
  endfunction

endclass
```
在 new 函數中，要將 invert 暫存器的寬度作為參數傳遞給 super.new 函數。
* super.new 函數
    * 第一個參數: **這裡的寬度並不是指這個暫存器的有效寬度，而是指這個暫存器中總共的位數**。如對於一個 16 位的暫存器，其中可能只使用了 8 位，那麼這裡要填寫的是 16，而不是 8。**這個數字一般與系統匯流排的寬度一致**
    * 第二個參數: super.new 中另外一個參數是是否要加入覆蓋率的支持，這裡選擇UVM_NO_COVERAGE，即不支持  
每一個派生自 uvm_reg 的類別都有一個 build，**這個 build 與 uvm_component 的 build_phase 並不一樣，它不會自動執行，而需要手動調用**，與 build_phase 相似的是所有的 uvm_reg_field都在這裡實例化。當 reg_data 實例化後，要呼叫 data.configure 函數來設定這個字段。
* data.configure 函數
    * 第一個參數: 就是此域（uvm_reg_field）的父輩，也就是此域位於哪個暫存器中，這裡當然是填寫 this 了
    * 第二個參數: 是此域的寬度，由於 DUT 中 invert 的寬度為 1，所以這裡為 1
    * 第三個參數: 是此域的最低位元在整個暫存器中的位置，從 0 開始計數。假如一個暫存器如圖7-4所示，其低 3 位元和高 5 位元沒有使使用，其中只有一個字段，此字段的有效寬度為 8 位，那麼在調用 configure 時，第二個參數就要填寫 8，第三個參數則要填寫 3，因為這 reg_field 是從第 4 位開始的
<img width="964" height="313" alt="image" src="https://github.com/user-attachments/assets/72615fc4-caf1-4979-b69d-94d9296d6072" />
    * 第四個參數表示此欄位的存取方式。 UVM 共支援如下 25 種存取方式：
1）RO：讀寫此域都無影響
2）RW：會盡量寫入，讀取時對此域無影響
3）RC：寫入時無影響，讀取時會清除
4）RS：寫入時無影響，讀取時會設定所有的位元
5）WRC：盡量寫入，讀取時會清零
6）WRS：盡量寫入，讀取時會設定所有的位元
7）WC：寫入時會清零，讀取時無影響
8）WS：寫入時會設定所有的位，讀取時無影響
9）WSRC：寫入時會設定所有的位，讀取時會清零
10）WCRS：寫入時會清零，讀取時會設定所有的位元
11）W1C：寫1清零，寫0時無影響，讀取時無影響
12）W1S：寫1設定所有的位，寫0時無影響，讀取時無影響
13）W1T：寫入1入時會翻轉，寫入0時無影響，讀取時無影響
14）W0C：寫0清零，寫1時無影響，讀取時無影響
15）W0S：寫0設定所有的位，寫1時無影響，讀取時無影響
16）W0T：寫入0入時會翻轉，寫1時無影響，讀取時無影響
17）W1SRC：寫1設定所有的位，寫0時無影響，讀清零
18）W1CRS：寫1清零，寫0時無影響，讀取設定所有位元
19）W0SRC：寫0設定所有的位，寫1時無影響，讀清零
20）W0CRS：寫入0清零，寫1時無影響，讀取設定所有位元
21）WO：盡可能寫入，讀取時會出錯
22）WOC：寫入時清零，讀取時發生錯誤
23）WOS：寫入時設定所有位，讀取時會發生錯誤
24）W1：重設（reset）後，第一次會盡量寫入，其他寫入無影響，讀取時無影響
25）WO1：重設後，第一次會盡量寫入，其他的寫入無影響，讀取時會出錯
事實上，暫存器的種類多種多樣，如上 25 種存取方式有時並不能滿足使用者的需求，這時就需要自訂暫存​​器的模型
    * 第五個參數表示是否是易失的（volatile），這個參數一般不會使用
    * 第六個參數表示此域上電重設後的預設值
    * 第七個參數表示此域是否有重位，一般的暫存器或暫存器的域都有上電重設值，因此這裡一般也填入 1
    * 第八個參數表示這個域是否可以隨機化。這主要用於對暫存器進行隨機寫入測試，如果選擇了 0，那麼此域將不會隨機化，而一直是重設值，否則將會隨機出一個數值來。這一個參數當且僅當第四個參數為 RW、WRC、WRS、WO、W1、WO1 時才有效
    * 第九個參數表示這個域是否可以單獨存取
定義好此暫存器後，需要在一個由 reg_block 派生的類別中將其實例化：
src/ch7/section7.2/reg_model.sv  
```  
class reg_model extends uvm_reg_block;
  rand reg_invert invert;

  virtual function void build();
    default_map = create_map("default_map", 0, 2, UVM_BIG_ENDIAN, 0);

    invert = reg_invert::type_id::create("invert", , get_full_name());
    invert.configure(this, null, "");
    invert.build();
    default_map.add_reg(invert, 'h9, "RW");
  endfunction

  `uvm_object_utils(reg_model)

  function new(input string name="reg_model");
    super.new(name, UVM_NO_COVERAGE);
  endfunction

endclass
```  
同 uvm_reg 衍生的類別一樣，每一個由 uvm_reg_block 衍生的類別也要定義一個 build 函數，一般在此函數中實作所有暫存器的實例化。一個 uvm_reg_block 中一定要對應一個 uvm_reg_map，系統已經有一個宣告好的 default_map，只需要在 build 中將其實例化。這個**實例化的過程並不是直接呼叫 uvm_reg_map 的 new 函數，而是透過呼叫 uvm_reg_block 的 create_map 來實現**， create_map 有眾多的參數，
* create_map 函數
    * 第一個參數是名字
    * 第二個參數是基底位址
    * 第三個參數則是系統匯流排的寬度，這裡的單位是byte而不是bit
    * 第四個參數是大小端，最後一個參數表示是否能夠依照 byte 定址。隨後實例化 invert 並呼叫 invert.configure 函數。這個函數的主要功能是指定暫存器進行後門存取操作時的路徑。
* data.configure 函數
    * 第一個參數是此暫存器所在 uvm_reg_block 的指針，這裡填入 this
    * 第二個參數是 reg_file 的指針（7.4.2節將會介紹 reg_file 的概念）這裡暫時填寫null
    * 第三個參數是此暫存器的後閘存取路徑，關於這點請參考 7.3 節，這裡暫且為空。
當調用完 configure 時，需要手動調用 invert 的 build 函數，將 invert 中的域實例化。最後一步則是將此暫存器加入 default_map 中。 **uvm_reg_map 的作用是儲存所有暫存器的位址**，因此必須將實例化的暫存器加入 default_map 中，否則無法進行前門存取操作。
* add_reg 函數
    * 第一個參數是要加入的暫存器
    * 第二個參數是暫存器的位址，這裡是16’h9
    * 第三個參數是此暫存器的存取方式
到此為止，一個簡單的暫存器模型已經完成。回顧前面介紹過的暫存器模型中的一些常用概念。
* uvm_reg_field 是最小的單位，是具體儲存暫存器數值的變量，可以直接用這個類別
* uvm_reg 則是一個"空殼子"，或者用專業名詞來說，它是一個純虛類，因此是不能直接使用的，必須由其派生一個新類，在這個新類別中至少加入一個 uvm_reg_field，然後這個新類別才可以使用
* uvm_reg_block 則是用來組織大量 uvm_reg 的一個大容器
打個比方說，uvm_reg 是一個小瓶子，其中必須裝上藥丸（uvm_reg_field）才有意義，這個裝藥丸的過程就是定義派生類的過程，而 uvm_reg_block 則是一個大箱子，它中可以放許多小瓶子（uvm_reg），也可以放其他稍微小一點的箱子（uvm_reg_block）。整個暫存器模型就是一個大箱子（uvm_reg_block）
