# 寄存器模型簡介
## 暫存器模型簡介
* **帶暫存器配置匯流排的 DUT**
先前所有的例子中，所使用的 DUT 幾乎都只有一組資料輸入輸出口，而沒有行為控制口，這樣的 DUT 幾乎是沒有任何價值的。通常來說，DUT 中會有一組控制端口，透過控制端口，可以配置 DUT 中的暫存器，
 DUT 可以根據暫存器的值來改變其行為。這組控制埠就是**暫存器配置匯流排**。如附錄 B 的程式碼清單 B-2 所示。
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
1. 在這個 DUT 中，只有一個 1 bit 的暫存器 invert，為其分配位址 16’h9。  
    如果它的值為1，那麼 DUT 在輸出時會將輸入的資料取反  
    如果為 0，則將輸入資料直接發送出去
2. invert 可以透過總線 bus_* 進行配置  
    bus_op 為 1 時表示寫操作  
    bus_op 為 0 表示讀取操作  
3. bus_addr 表示位址，bus_rd_data 表示讀取的數據，bus_wr_data 表示要寫入的數據
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
需要說明的是，如果是讀取操作，這裡直接將讀到的資料賦值給 rd_data。在 sequence 中，可以使用以下方式進行讀取操作：  
src/ch7/section7.1/7.1.1/my_case0.sv
```
virtual task body();
  `uvm_do_with(m_trans, {m_trans.addr == 16'h9;
                         m_trans.bus_op == BUS_RD;})
  `uvm_info("case0_bus_seq", $sformatf("invert's initial value is %0h", m_trans.rd_data), UVM_LOW)
endtask
```
這裡用到了6.7.3節介紹的另類的response，在sequence中直接引用m_trans.rd_data可以得到讀取資料的值。  
以如下的方式進行寫入操作：
```
virtual task body();
  `uvm_do_with(m_trans, {m_trans.addr == 16'h9;
                         m_trans.bus_op == BUS_WR;
                         m_trans.wr_data == 16'h1;})
endtask
```
現在，整個驗證平台的框圖變成如圖7-1所示的形式。
<img width="1148" height="812" alt="image" src="https://github.com/user-attachments/assets/45d0f449-afdb-4864-a727-e1b974d0ce7c" />  
* **需要寄存器模型才能做的事情**  
考慮下一個問題，在上節所示的 DUT 中，invert 暫存器用於控制 DUT 是否將輸入的激勵位元取反。
在取反的情況下，參考模型需要讀取此暫存器的值，如果為 1，那麼其輸出 transaction 也需要進行反轉。
可是如何在參考模型中讀取一個暫存器的值呢？
就目前讀者所掌握的知識來說，只能先透過使用 bus_driver 向總線上發送讀取指令，並給出要讀的暫存器位址來查看一個暫存器的值。
要實現這個過程，需要啟動一個 sequence，這個 sequence 會發送一個 transaction 給 bus_driver。所以第一個問題是如何在參考
模型的控制下來啟動一個 sequence 以讀取暫存器。第二個問題是，sequence 讀取的暫存器的值如何傳遞給參考模型。
對於第一個問題，一個簡單的想法是設定一個全域事件（又是全域變數！），然後在參考模型中觸發這個事件。在virtual
sequence中等待這個事件的到來，等到了，則啟動sequence。這裡用到了全域變量，這是相當忌諱的。
如果不使用全域變量，那麼可以用一個非全域事件來取代。利用config機制分別為virtual sequencer和scoreboard設定一個
config_object，在此object中設定一個事件，例如rd_reg_event，然後在scoreboard中觸發這個事件，而在virtual sequence中則要等待這
個事件的到來：
```
@p_sequencer.config_object.rd_reg_event;
```
這個事件等到後就啟動一個 sequence，開始讀取暫存器。
對於第二個問題，當 sequence 讀取到暫存器後，可以再透過6.6.2節所示的 config_db 傳遞給參考模型，在參考模型中使用6.6.3
節所示的 wait_modified 來更新資料。
從上面可以看出這個過程相當麻煩。在一個大的設計中，其暫存器有數百上千個。為了區分這麼多的暫存器，又需要許多其
他額外的設定。其實，這個讀取過程可以使用暫存器模型來實作。如果有了寄存器模型，那麼這個過程就可以簡化為：
```
task my_model::main_phase(uvm_phase phase);
…
reg_model.INVERT_REG.read(status, value, UVM_FRONTDOOR);
…
endtask
```
只要一條語句就可以實現上述複雜的過程。像是啟動sequence及將讀取結果回傳這些事情，都會由暫存器模型來自動完成。
圖7-2顯示了讀取暫存器的過程，其中左圖為不使用暫存器模型，右圖為使用暫存器模型的讀取方式。
在沒有暫存器模型之前，只能啟動sequence透過前門（FRONTDOOR）存取的方式來讀取暫存器，局限較大，在
scoreboard（或其他component）中難以控制。而有了暫存器模型之後，scoreboard只與暫存器模型打交道，無論是發送讀取的指令
還是取得讀取操作的回傳值，都可以由暫存器模型完成。有了暫存器模型後，可以在任何耗費時間的phase中使用暫存器模型以前閘
存取或後門（BACKDOOR）存取的方式來讀取暫存器的值，同時還能在某些不耗費時間的phase（如check_phase）中使用後門訪
問的方式來讀取暫存器的值。
前門存取與後門存取是兩種暫存器的存取方式。所謂前門訪問，指的是透過模擬cpu在總線上發出讀取指令，進行讀寫操作。在
這個過程中，模擬時間（$time函數得到的時間）是一直往前走的。
<img width="1182" height="770" alt="image" src="https://github.com/user-attachments/assets/7278cf97-fc0d-4cf5-822b-d8641380e1ca" />  
而後門訪問是與前門訪問相對的概念。它不是透過總線進行讀寫操作，而是直接透過層次化的引用來改變暫存器的值。關於
前門訪問與後門訪問的問題，將會在7.3節中詳細說明。
另外，暫存器模型也提供一些任務，如mirror、update，它們可以批次完成暫存器模型與DUT中相關暫存器的交互作用。
可見，UVM暫存器模型的本質就是重新定義了驗證平台與DUT的暫存器接口，使驗證人員能更好地組織及配置暫存器，簡化流
程、減少工作量。
* **暫存器模型中的基本概念**
