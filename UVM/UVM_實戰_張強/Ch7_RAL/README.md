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
* **將寄存器模型整合到驗證平台中**
暫存器模型的前門存取方式工作流程如圖 7-5 所示，其中圖 a 為讀取操作，圖 b 為寫入操作：
<img width="1194" height="739" alt="image" src="https://github.com/user-attachments/assets/bed2cd08-8ea4-4dca-92f8-fff73ae17099" />  
暫存器模型的前門存取操作可以分成讀取和寫入兩種。無論是讀或寫，暫存器模型都會透過 sequence 產生一個 uvm_reg_bus_op 的變量，此變數中儲存操作類型（讀取或寫入）和操作的位址，如果是寫入操作，還會有要寫入的資料。此變數中的資訊要經過一個轉換器（adapter）轉換後交給 bus_sequencer，隨後交給 bus_driver，由 bus_driver 實作最終的前門存取讀寫操作。因此，必須要定義好一個轉換器。如下例為一個簡單的轉換器的程式碼：
src/ch7/section7.2/my_adapter.sv
  
```
class my_adapter extends uvm_reg_adapter;
  string tID = get_type_name();

  `uvm_object_utils(my_adapter)

  function new(string name="my_adapter");
    super.new(name);
  endfunction : new

  function uvm_sequence_item reg2bus(const ref uvm_reg_bus_op rw);
    bus_transaction tr;
    tr = new("tr");
    tr.addr = rw.addr;
    tr.bus_op = (rw.kind == UVM_READ) ? BUS_RD : BUS_WR;
    if (tr.bus_op == BUS_WR)
      tr.wr_data = rw.data;
    return tr;
  endfunction : reg2bus

  function void bus2reg(uvm_sequence_item bus_item, ref uvm_reg_bus_op rw);
    bus_transaction tr;
    if(!$cast(tr, bus_item)) begin
      `uvm_fatal(tID, "Provided bus_item is not of the correct type. Expecting bus_transaction")
      return;
    end
    rw.kind = (tr.bus_op == BUS_RD) ? UVM_READ : UVM_WRITE;
    rw.addr = tr.addr;
    rw.byte_en = 'h3;
    rw.data = (tr.bus_op == BUS_RD) ? tr.rd_data : tr.wr_data;
    rw.status = UVM_IS_OK;
  endfunction : bus2reg

endclass : my_adapter
```
  
一個轉換器要定義好兩個函數，一是 **reg2bus，其作用為將暫存器模型透過 sequence 發出的 uvm_reg_bus_op 型的變數轉換成 bus_sequencer 能夠接受的形式**，二是 **bus2reg，其作用為當監測到總線上有操作時，它將收集來的 transaction 轉換成寄存器模型能夠接受的形式，以便暫存器模型能夠更新對應的暫存器的值**。說到這裡，不得不考慮暫存器模型發起的讀取操作的數值是如何傳回給暫存器模型的？由於總線的特殊性，bus_driver 在驅動總線進行讀取操作時，它也能順便取得要讀的數值，如果它將此值放入從 bus_sequencer 獲得的 bus_transaction 中時，那麼 bus_transaction 中就會有讀取的值，此值經過 adapter 的 bus2reg 函數的傳遞，最後被暫存器模型獲取，這個過程如圖 7-5a 所示。由於並沒有實際的 transaction 的傳遞，所以從 driver 到 adapter 使用了虛線。轉換器寫好之後，就可以在 base_test 中加入暫存器模型了：
src/ch7/section7.2/base_test.sv
  
```
class base_test extends uvm_test;

  my_env env;
  my_vsqr v_sqr;
  reg_model rm;  // 新加的 reg model
  my_adapter reg_sqr_adapter;  // 新加的 reg sqr adapter
…
  extern function new(string name = "base_test", uvm_component parent = null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);

endclass

function void base_test::build_phase(uvm_phase phase);
  super.build_phase(phase);
  env = my_env::type_id::create("env", this);
  v_sqr = my_vsqr::type_id::create("v_sqr", this);
  rm = reg_model::type_id::create("rm", this);
  rm.configure(null, "");
  rm.build();
  rm.lock_model();
  rm.reset();
  reg_sqr_adapter = new("reg_sqr_adapter");
  env.p_rm = this.rm;
endfunction

function void base_test::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  v_sqr.p_my_sqr = env.i_agt.sqr;
  v_sqr.p_bus_sqr = env.bus_agt.sqr;
  v_sqr.p_rm = this.rm;
  rm.default_map.set_sequencer(env.bus_agt.sqr, reg_sqr_adapter);
  rm.default_map.set_auto_predict(1);
endfunction
```
  
要將一個暫存器模型整合到 base_test 中，那麼至少需要在 base_test 中定義兩個成員變量，一是 reg_model，另外一個就是 reg_sqr_adapter。將所有用到的類別在 build_phase 中實例化。在實例化後 reg_model 還要做四件事：
* 第一個是呼叫 configure 函數，其第一個參數是 parent block，由於是最頂層的 reg_block，因此填入 null，第二個參數是後門訪問路徑，請參考7.3節，這裡傳入一個空的字串
* 第二是呼叫 build 函數，將所有的暫存器實例化
* 第三是呼叫 lock_model 函數，呼叫此函數後，reg_model 中就不能再加入新的寄存器了
* 第四是呼叫 reset 函數，如果不呼叫此函數，那麼 reg_model 中所有暫存器的值都是 0，呼叫此函數後，所有暫存器的值都將變為設定的重設值  
暫存器模型的前門存取操作最終都會由 uvm_reg_map 完成，因此在 connect_phase 中，需要將轉換器和 bus_sequencer 通過 set_sequencer 函數告知 reg_model 的 default_map，並將 default_map 設定為自動預測狀態
  
* **在驗證平台中使用暫存器模型**
當一個暫存器模型被建立好後，可以在 sequence 和其他 component 中使用。以在參考模型中使用為例，需要在參考模型中有一個暫存器模型的指標：
src/ch7/section7.2/my_model.sv
  
```
class my_model extends uvm_component;
…
  reg_model p_rm;
…
endclass
```
  
在程式碼清單 7-10 中已經為 env 的 p_rm 賦值，因此只需要在 env 中將 p_rm 傳遞給參考模型即可：
src/ch7/section7.2/my_env.sv
  
```
function void my_env::connect_phase(uvm_phase phase);
…
  mdl.p_rm = this.p_rm;
endfunction
```
  
對於暫存器，暫存器模型提供了兩個基本的任務：read 和 write。若要在參考模型中讀取暫存器，使用 read 任務：
src/ch7/section7.2/my_model.sv

```
task my_model::main_phase(uvm_phase phase);
  my_transaction tr;
  my_transaction new_tr;
  uvm_status_e status;
  uvm_reg_data_t value;

  super.main_phase(phase);
  
  // 從寄存器模型讀取初始值
  p_rm.invert.read(status, value, UVM_FRONTDOOR);

  while(1) begin
    port.get(tr);
    new_tr = new("new_tr");
    new_tr.copy(tr);

    // 如果 invert 寄存器的值為非零，則進行翻轉處理
    if(value)
      invert_tr(new_tr);

    ap.write(new_tr);
  end
endtask
```

read 任務的原型如下圖所示：
UVM source code
  
```
extern virtual task read(output uvm_status_e status,
                          output uvm_reg_data_t value,
                          input uvm_path_e path = UVM_DEFAULT_PATH,
                          input uvm_reg_map map = null,
                          input uvm_sequence_base parent = null,
                          input int prior = -1,
                          input uvm_object extension = null,
                          input string fname = "",
                          input int lineno = 0);
```

它有多個參數，常用的是其前三個參數。
* 第一個是 uvm_status_e 型的變量，這是一個輸出，用來表明讀取操作是否成功
* 第二個是讀取的數值，也是輸出
* 第三個是讀取的方式，可選 UVM_FRONTDOOR 和 UVM_BACKDOOR
由於參考模型一般不會寫入暫存器，因此對於 write 任務，以在 virtual sequence 進行寫入操作為例說明。在 sequence 中使用暫存器模型，通常透過 p_sequencer 的形式引用。需要先在 sequencer 中有一個暫存器模型的指針，程式碼清單 7-10 中已經為 v_sqr.p_rm 賦值了。因此可以直接以如下方式進行寫入操作：
src/ch7/section7.2/my_case0.sv

```
class case0_cfg_vseq extends uvm_sequence;
…
  virtual task body();
    uvm_status_e status;
    uvm_reg_data_t value;
  …
    // 透過 sequencer 中的寄存器模型指標 (p_rm) 進行前門存取寫入
    p_sequencer.p_rm.invert.write(status, 1, UVM_FRONTDOOR);
  …
  endtask
endclass
```

write 任務的原型如下圖所示：
  
```
extern virtual task write(output uvm_status_e status,
                          input uvm_reg_data_t value,
                          input uvm_path_e path = UVM_DEFAULT_PATH,
                          input uvm_reg_map map = null,
                          input uvm_sequence_base parent = null,
                          input int prior = -1,
                          input uvm_object extension = null,
                          input string fname = "",
                          input int lineno = 0);
```

它的參數也有很多個，但是與 read 類似，常用的只有前三個。
* 第一個為 uvm_status_e 型的變量，這是一個輸出，用於表明寫操作是否成功
* 第二個要寫的值，是一個輸入
* 第三個是寫入操作的方式，可選 UVM_FRONTDOOR 和 UVM_BACKDOOR 
暫存器模型對 sequence 的 transaction 類型沒有任何要求。因此，可以在一個發送 my_transaction 的 sequence 中使用暫存器模型對暫存器進行讀寫操作
## 後門訪問與前門訪問
* **UVM 中前門存取的實現**
所謂前門存取操作就是透過暫存器配置匯流排（如 APB 協定、OCP 協定、I2C 協定等）來對 DUT 進行操作。無論在任何總線協議中，前門存取操作只有兩種：**讀取操作**和**寫入操作**。前門訪問操作是比較正統的用法。對一塊實際焊接在電路板上正常運作的晶片來說，此時若要存取其中的某些暫存器，前門存取操作是唯一的方法。在 7.1.2 節介紹暫存器模型時曾經講過，對於參考模型來說，最大的問題是如何在其中啟動一個 sequence，當時列舉了全局變數和 config_db 的兩種方式。除了這兩種方式之外，如果能夠在參考模型中得到一個 sequencer 的指針，也可以在此 sequencer 上啟動一個 sequence。這通常比較容易實現，只要在其中設定一個 p_sqr 的變量，並在 env 中將 sequencer 的指標賦值給此變數即可。接下來的關鍵就是分別寫一個讀寫的 sequence：
src/ch7/section7.2/7.3.1/reg_access_sequence.sv

```
class reg_access_sequence extends uvm_sequence#(bus_transaction);
  string tID = get_type_name();

  bit[15:0] addr;
  bit[15:0] rdata;
  bit[15:0] wdata;
  bit is_wr;
…
  virtual task body();
    bus_transaction tr;
    tr = new("tr");
    tr.addr = this.addr;
    tr.wr_data = this.wdata;
    tr.bus_op = (is_wr) ? BUS_WR : BUS_RD;

    `uvm_info(tID, $sformatf("begin to access register: is_wr = %0d, addr = %0h", is_wr, addr), UVM_MEDIUM)
    `uvm_send(tr)
    `uvm_info(tID, "successful access register", UVM_MEDIUM)

    this.rdata = tr.rd_data;
  endtask

endclass
```

之後，在參考模型中使用如下的方式來進行讀取操作：

```
task my_model::main_phase(uvm_phase phase);
…
  reg_access_sequence reg_seq;
  super.main_phase(phase);
  // 建立並啟動寄存器存取 sequence
  reg_seq = new("reg_seq");
  reg_seq.addr = 16'h9;
  reg_seq.is_wr = 0;
  reg_seq.start(p_sqr);

  while(1) begin
    // … 此處應有交易獲取邏輯 (如 port.get) …
    
    // 根據讀取到的寄存器數值決定是否翻轉交易
    if(reg_seq.rdata)
      invert_tr(new_tr);
      
    ap.write(new_tr);
  end
endtask
```

sequence 是自動執行的，但是在其執​​行完畢後（body 及 post_body 呼叫完成），為此 sequence 分配的記憶體仍然是有效的，所以可以使用 reg_seq 繼續引用此 sequence。上述讀取操作正是用到了這一點。對 UVM 來說，其在寄存器模型中使用的方式也與此類似。上述操作方式的關鍵是在參考模型中有一個 sequencer 的指針，而在在暫存器模型中也有一個這樣的指針，它就是 7.2.2 節中，在 base_test 的 connect_phase 為 default map 設定的 sequencer 指針。當然，對於 UVM 來說，它是一種通用的驗證方法學，所以要能夠處理各種 transaction 類型。幸運的是，這些要處理的
 transaction 都非常相似，在綜合了它們的特徵後，UVM 內建了一種 transaction：uvm_reg_item。透過 adapter 的 bus2reg 及 reg2bus，可以實現 uvm_reg_item 與目標 transaction 的轉換。以讀取操作為例，其完整的流程為：
* 參考模型呼叫暫存器模型的讀取任務
* 暫存器模型產生 sequence，並產生 uvm_reg_item：rw
* 產生 driver 能夠接受的 transaction：bus_req=adapter.reg2bus（rw）
* 把 bus_req 交給 bus_sequencer
* driver 得到 bus_req 後驅動它，得到讀取的值，並將讀取值放入 bus_req 中，呼叫 item_done
* 暫存器模型呼叫 adapter.bus2reg（bus_req，rw）將 bus_req 中的讀取值傳遞給 rw
* 將 rw 中的讀取資料回傳參考模型
在 6.7.2 節介紹 sequence 的應答機制時提到過，如果 driver 一直發送應答而 sequence 不收集應答，那麼將會導致 sequencer 的應答案隊列溢出。UVM 考慮到這種情況，在 adapter 中設定了 provide_responses 選項：
UVM source code

```
virtual class uvm_reg_adapter extends uvm_object;
…
  bit provides_responses;
…
endclass
```

在設定了此選項後，暫存器模型在呼叫 bus2reg 將目標 transaction 轉換成 uvm_reg_item 時，其傳入的參數是 rsp，而不是 req。使用應答機制的操作流程為：
* 參考模型呼叫暫存器模型的讀取任務
* 暫存器模型產生 sequence，並產生 uvm_reg_item：rw
* 產生 driver 能夠接受的 transaction：bus_req=adapter.reg2bus（rw）
* 將 bus_req 交給 bus_sequencer
* driver 得到 bus_req，驅動它，得到讀取的值，並將讀取值放入 rsp 中，呼叫 item_done
* 暫存器模型呼叫 adapter.bus2reg（rsp，rw）將 rsp 中的讀取值傳遞給 rw
* 將 rw 中的讀取資料回傳參考模型

* **後門存取操作的定義**
為了講述後門存取操作，從本節開始，將在 7.1.1 節的 DUT 的基礎上引入一個新的 DUT，如附錄 B 的程式碼清單 B-3 所示。這個 DUT 中加入了暫存器 counter。它的功能就是統計 rx_dv 為高電位的時脈數。在通訊系統中，有大量計數器用於統計各種包裹的數量，如超長包、長包、中包、短包、超短包等。這些計數器的一個共同的特點是它們是唯讀的，DUT 的匯流排介面無法透過前門存取操作對其進行寫入操作。除了是唯讀外，這些暫存器的位寬一般都比較寬，如32位、48位或64位等，它們的位寬超過了設計中對加法器寬度的上限限制。計數器在計數過程中需要使用加法器，對於加法器來說，在同等製程下，位寬越寬則其時序越差，因此在設計上一般會規定加法器的最大位寬。在上述DUT中，加法器的位寬被限制在16位。要實現 32 位元的 counter 的加法操作，需要使用兩個疊加的16位元加法器。為 counter 指派 16‘h5 和 16’h6 的位址，採用大端格式將高位元資料存放在低位址。此計數器是可讀的，另外可以對其進行寫入 1 清 0 操作。如果對其寫入其他數值，則不會起作用。後門存取是與前門存取相對的操作，從廣義上來說，所有不透過 DUT 的匯流排而對 DUT 內部的暫存器或記憶體進行存取的操作都是後門訪問操作。如在 top_tb 中可以使用下列方式對 counter 賦初值：
src/ch7/section7.3/7.3.2/top_tb.sv
  
```
initial begin
  @(posedge rst_n);
  my_dut.counter = 32'hFFFD;
end
```

所有後門存取操作都是不消耗模擬時間（即 $time 列印的時間）而只消耗運行時間的。這是後門訪問操作的最大優勢。既然有了前門訪問操作，那麼為什麼還需要後門訪問操作呢？後門訪問操作存在的意義在於：
* 後門訪問操作能夠更好地完成前門訪問操作所做的事情。**後門存取不消耗模擬時間**，與前門存取操作相比，它消耗的運行時間要遠小於前門訪問操作的運行時間。在一個大型晶片的驗證中，在其正常工作前需要配置眾多的寄存器，配置時間可能要達到一個或幾個小時，而如果使用後門訪問操作，則時間可能會縮短為原來的1/100
* **後門訪問操作能夠完成前門訪問操作不能完成的事情**。如在網路通訊系統中，計數器通常都是唯讀的（有些會附加清零功能），無法對其指定一個非零的初值。而大部分計數器都是多個加法器的疊加，需要測試它們的進位操作。本節 DUT 的 counter 使用了兩個疊加的 16 位元加法器，需要測試當計數到 32‘hFFFF 時能否順利進位成為 32’h1_0000，這可以透過延長模擬時間使其計數到 32‘hFFFF，這在本節的 DUT 中是可以的，因為計數器每個時脈都加 1。但是在實際應用中，可能要幾萬個或更多的時鐘才會加 1，因此需要大量的運行時間，如幾天。這只是 32 位元加法器的情況，如果是 48 位元的計數器，情況則會更糟。這種情況下，後閘存取操作能夠完成前門存取作業完成的事情，給唯讀的暫存器一個初值  
當然，與前門訪問操作相比，後門訪問操作也有其劣勢。如所有的前門存取操作都可以在波形檔案中找到總線訊號變化的波形及所有操作的記錄。但是**後門存取操作則無法在波形檔案中找到操作痕跡**。**其操作記錄只能仰仗驗證平台編寫者在進行後門訪問操作時輸出的列印訊息**，這樣便增加了調試的難度

* **使用interface進行後門存取操作**
上一節中提到在 top_tb 中使用絕對路徑對寄存器進行後門存取操作，這需要更改 top_tb.sv 文件，但是這個文件一般是固定的，不會因測試案例的不同而變化，所以這種方式的可操作性不強。在 driver 等元件中也可以使用這種絕對路徑的方式來進行後門訪問操作，但強烈建議不要在 driver 等驗證平台的元件中使用絕對路徑。這種方式的可移植性不強。如果想在 driver 或 monitor 中使用後門訪問，一種方法是使用介面。可以新建一個後門 interface：
src/ch7/section7.3/7.3.3/backdoor_if.sv

```
interface backdoor_if(input clk, input rst_n);

  function void poke_counter(input bit[31:0] value);
    top_tb.my_dut.counter = value;
  endfunction

  function void peek_counter(output bit[31:0] value);
    value = top_tb.my_dut.counter;
  endfunction

endinterface
```

poke_counter 為後門寫，而 peek_counter 為後門讀。在測試用例（或 drvier、scoreboard ）中，若要對暫存器賦初值可以直接呼叫此函數：

```
task my_case0::configure_phase(uvm_phase phase);
  phase.raise_objection(this);
  @(posedge vif.rst_n);
  vif.poke_counter(32'hFFFD);
  phase.drop_objection(this);
endtask
```

如果有 n 個寄存器，那麼需要寫 n 個 poke 函數，同時如果有讀取要求的話，還要寫 n 個 peek 函數，這限制了其使用，且此文件完全沒有任何移植性。這種方式在實際中是有應用的，它適用於不想使用寄存器模型提供的後門存取或根本不想建立寄存器模型，同時又必須要對 DUT 中的一個暫存器或一塊記憶體（memory）進行後門存取操作的情況。

* **UVM中後門存取操作的實作：DPI+VPI**
在 7.3.2 節和 7.3.3 節提供了兩種廣義的後門存取方式，它們的共同點即都是在 SystemVerilog 中實現的。但是在實際的驗證平台中，還有在 C/C++ 程式碼中對 DUT 中的暫存器進行讀寫的需求。Verilog 提供 VPI 接口，可以將 DUT 的層次結構開放給外部的 C/C++ 代碼。常用的 VPI 介面有以下兩個：

```
vpi_get_value(obj, p_value);
vpi_put_value(obj, p_value, p_time, flags);
```

其中 vpi_get_value 用於從 RTL 中得到一個暫存器的值。vpi_put_value 用於將 RTL 中的暫存器設定為某個值。但是如果單純地使用 VPI 進行後門存取操作，在 SystemVerilog 與 C/C++ 之間傳遞參數時將非常麻煩。VPI 是 Verilog 提供的接口，為了呼叫 C/C++ 中的函數，提供更好的使用者體驗，SystemVerilog 提供了一個更好的介面：DPI。如果使用 DPI，以讀取操作為例，在 C/C++ 中定義如下一個函數：

```
int uvm_hdl_read(char *path, p_vpi_vecval value);
```

