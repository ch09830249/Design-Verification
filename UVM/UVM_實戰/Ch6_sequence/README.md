# sequence 基礎
## 從 driver 中剝離激勵產生功能
最開始時，driver的main_phase是這樣的：
```
task my_driver::main_phase(uvm_phase phase);
  my_transaction tr;
  phase.raise_objection(this);
  for(int i = 0; i < 10; i++) begin
    tr = new;
    assert(tr.randomize);
    drive_one_pkt(tr);
  end
  phase.drop_objection(this);
endtask
```
如果只是**施加上述一種激勵**，這樣是可以的。但**當要對 DUT 施加不同的激勵時**，那該怎麼辦呢？上述程式碼中是施加了正確
的包，而下一次測試中**要在第 9 個 transaction 中加入CRC錯誤的包**，那麼可以這麼寫：
```
task my_driver::main_phase(uvm_phase phase);
  my_transaction tr;
  phase.raise_objection(this);
  for(int i = 0; i < 10; i++) begin
    tr = new;
    if(i == 8)
      assert(tr.randomize with {tr.crc_err == 1;});
    else
      assert(tr.randomize);
    drive_one_pkt(tr);
  end
  phase.drop_objection(this);
endtask
```
**這就相當於將整個 main_phase 重新寫了一遍**。如果現在有了新的需求，需要再測一個超長包。那麼，就需要再次改寫 
main_phase ，也就是說，**每多測一種情況，就要多改寫一次 main_phase**。如果經常改寫某個任務或函數，那麼就很容易將之前對
的地方改錯。所以說，這種方法是不可取的，因為它的可擴展性太差，會常常帶來錯誤。
**仔細觀察 main_phase，其實只有從 tr=new 語句到 drive_one_pkt 之間的語句在變**。有沒有什麼方法可以將這些語句從 main_phase 
中獨立出來呢？最好的方法就是在不同的測試案例中決定這幾行語句的內容。這種想法中已經包含了激勵的產生與驅動的分離這
個觀點。 drive_one_pkt 是驅動，這是 driver 應該做的事情，但是**像產生什麼樣的包、如何產生等這些事情應該從 driver 中獨立出去**。
## sequence 的啟動與執行
當完成一個 sequence 的定義後，可以使用 start 任務將其啟動：
```
my_sequence my_seq;
my_seq = my_sequence::type_id::create("my_seq");
my_seq.start(sequencer);
```
除了直接啟動之外，還可以使用 default_sequence 啟動。事實上 default_sequence 會呼叫 start 任務，它有兩種呼叫方式，其中一
種是前文已經介紹過的：
```
// 設定該 sequencer 的 default sequence 為 case0_sequence
uvm_config_db#(uvm_object_wrapper)::set(this,
                                        "env.i_agt.sqr.main_phase",
                                        "default_sequence",
                                        case0_sequence::type_id::get());
```
另外一種方式是先實例化要啟動的 sequence，之後再透過 default_sequence 啟動：
```
function void my_case0::build_phase(uvm_phase phase);
  ase0_sequence cseq;
  super.build_phase(phase);
  cseq = new("cseq");
  uvm_config_db#(uvm_sequence_base)::set(this,
                                        "env.i_agt.sqr.main_phase",
                                        "default_sequence",
                                        cseq);    // 透過實例化的 instance 來做設定
endfunction
```
當一個 sequence 啟動後會自動執行 sequence 的 body 任務。其實，除了 body 外，還會自動呼叫 sequence 的 pre_body 與 post_body：
```
class case0_sequence extends uvm_sequence #(my_transaction);
......
  virtual task pre_body();
    `uvm_info("sequence0", "pre_body is called!!!", UVM_LOW)
  endtask

  virtual task post_body();
    `uvm_info("sequence0", "post_body is called!!!", UVM_LOW)
  endtask

  virtual task body();
......
    #100;
    `uvm_info("sequence0", "body is called!!!", UVM_LOW)
  endtask
......
  `uvm_object_utils(case0_sequence)
endclass
```
```
# UVM_INFO my_case0.sv(11) @ 0: uvm_test_top.env.i_agt.sqr@@cseq [sequence0] pre_body is called!!!
# UVM_INFO my_case0.sv(22) @ 100000: uvm_test_top.env.i_agt.sqr@@cseq [sequence0] body is called!!!
# UVM_INFO my_case0.sv(15) @ 100000: uvm_test_top.env.i_agt.sqr@@cseq [sequence0] post_body is called
```
# sequence 的仲裁機制
## 在同一 sequencer 上啟動多個 sequence
在前文所有的例子中，同一時刻，在同一 sequencer 上只啟動了一個 sequence。事實上，**UVM 支援同一時刻在同一 sequencer 上
啟動多個 sequence**。
在 my_sequencer 上同時啟動了兩個 sequence：sequence1 和sequence2，程式碼如下所示：
```
task my_case0::main_phase(uvm_phase phase);
  sequence0 seq0;
  sequence1 seq1;

  seq0 = new("seq0");
  seq0.starting_phase = phase;
  seq1 = new("seq1");
  seq1.starting_phase = phase;

  fork
    seq0.start(env.i_agt.sqr);
    seq1.start(env.i_agt.sqr);
  join
endtask
```
其中 sequence0 的定義為：
```
class sequence0 extends uvm_sequence #(my_transaction);

  virtual task body();
    ...
    repeat (5) begin
      `uvm_do(m_trans)
      `uvm_info("sequence0", "send one transaction", UVM_MEDIUM)
    end
    #100;
    ...
  endtask

  `uvm_object_utils(sequence0)
endclass
```
sequence1 的定義為：
```
class sequence1 extends uvm_sequence #(my_transaction);

  virtual task body();
    ...
    repeat (5) begin
      `uvm_do_with(m_trans, {m_trans.pload.size < 500;})
      `uvm_info("sequence1", "send one transaction", UVM_MEDIUM)
    end
    #100;
    ...
  endtask

  `uvm_object_utils(sequence1)
endclass
```
運行如上程式碼後，會顯示兩個 sequence 交替產生 transaction：
```
# UVM_INFO my_case0.sv(15) @ 85900: uvm_test_top.env.i_agt.sqr@@seq0 [sequence0] send one transaction
# UVM_INFO my_case0.sv(37) @ 112500: uvm_test_top.env.i_agt.sqr@@seq1 [sequence1] send one transaction
# UVM_INFO my_case0.sv(15) @ 149300: uvm_test_top.env.i_agt.sqr@@seq0 [sequence0] send one transaction
# UVM_INFO my_case0.sv(37) @ 200500: uvm_test_top.env.i_agt.sqr@@seq1 [sequence1] send one transaction
# UVM_INFO my_case0.sv(15) @ 380700: uvm_test_top.env.i_agt.sqr@@seq0 [sequence0] send one transaction
# UVM_INFO my_case0.sv(37) @ 436500: uvm_test_top.env.i_agt.sqr@@seq1 [sequence1] send one transaction
```
sequencer 根據什麼選擇使用哪個 sequence 的 transaction 呢？這是 UVM 的 sequence 機制中的仲裁問題。對於 transaction 來說，存在
優先順序的概念，通常來說，優先順序越高越容易被選中。
**當使用 uvm_do 或 uvm_do_with 巨集時，產生的 transaction 的優先權是預設的優先級，即-1**。  
**可以透過 uvm_do_pri 及 uvm_do_pri_with 來改變所產生的 transaction 的優先權**：
```
class sequence0 extends uvm_sequence #(my_transaction);

  virtual task body();
    ...
    repeat (5) begin
      `uvm_do_pri(m_trans, 100)    // here
      `uvm_info("sequence0", "send one transaction", UVM_MEDIUM)
    end
    #100;
    ...
  endtask

endclass

class sequence1 extends uvm_sequence #(my_transaction);

  virtual task body();
    ...
    repeat (5) begin
      `uvm_do_pri_with(m_trans, 200, {m_trans.pload.size < 500;})     // here
      `uvm_info("sequence1", "send one transaction", UVM_MEDIUM)
    end
    ...
  endtask

endclass
```
**uvm_do_pri 與 uvm_do_pri_with 的第二個參數是優先權，這個數值必須是一個大於等於-1的整數。數字越大，優先權越高。**  
由於 sequence1 中 transaction 的優先權較高，所以如預期，先選擇 sequence1 產生的 transaction。當 sequence1 的 transaction 全部
生成完畢後，再產生 sequence0 的 transaction。但是運行上述程式碼，發現並沒有如預期的那樣，而是 sequence0 與 sequence1 交替產生 
transaction 。這是因為 sequencer 的仲裁演算法有很多種：
```
SEQ_ARB_FIFO,
SEQ_ARB_WEIGHTED,
SEQ_ARB_RANDOM,
SEQ_ARB_STRICT_FIFO,
SEQ_ARB_STRICT_RANDOM,
SEQ_ARB_USER
```
在預設情況下 sequencer 的仲裁演算法是 SEQ_ARB_FIFO。  
**SEQ_ARB_FIFO** 它會嚴格遵循先入先出的順序，而不會考慮優先順序。  
**SEQ_ARB_WEIGHTED** 是加權的仲裁；  
**SEQ_ARB_RANDOM** 是完全隨機選擇；  
**SEQ_ARB_STRICT_FIFO** 是嚴格依照優先順序的，當有多個相同優先權的 sequence 時，按照先入先出的順序選擇；  
**SEQ_ARB_STRICT_RANDOM** 是嚴格依照優先權的，當有多個同一優先順序的sequence時，隨機從最高優先權中選擇；
**SEQ_ARB_USER** 則是使用者可以自訂新的仲裁演算法。
因此，若想使優先權起作用，應該設定仲裁演算法為 SEQ_ARB_STRICT_FIFO 或 SEQ_ARB_STRICT_RANDOM：
```
task my_case0::main_phase(uvm_phase phase);
  ...
  env.i_agt.sqr.set_arbitration(SEQ_ARB_STRICT_FIFO);  // 設定仲裁策略
  fork
    seq0.start(env.i_agt.sqr);
    seq1.start(env.i_agt.sqr);
  join
endtask
```
經過如上的設定後，會發現直到 sequence1 發送完 transaction 後，sequence0 才開始發送。
除 transaction 有優先權外，sequence 也有優先權的概念。可以在 sequence 啟動時指定其優先權：
```
task my_case0::main_phase(uvm_phase phase);
  ...
  env.i_agt.sqr.set_arbitration(SEQ_ARB_STRICT_FIFO);
  fork
    seq0.start(env.i_agt.sqr, null, 100);
    seq1.start(env.i_agt.sqr, null, 200);
  join
endtask
```
start 任務的第一個參數是 sequencer，第二個參數是 parent sequence，可以設定為 null，第三個參數是優先權，如果不指定則此
值為-1，它同樣不能設定為一個小於 -1 的數字。
sequence0 和 sequence1，即不在 uvm_do 系列巨集中指定優先權。運行上述程式碼，會發現 
sequence1 中的 transaction 完全發送完後才發送 sequence0 中的 transaction。所以，對 sequence 設定優先權的本質即設定其內產生的 
transaction 的優先權。
## sequencer 的 lock 操作
當多個 sequence 在一個 sequencer 上同時啟動時，每個 sequence 產生的 transaction 都需要參與 sequencer 的仲裁。那麼考慮這樣
一種情況，**某個 sequence 比較奇特，一旦它要執行，那麼它所有的 transaction 必須連續地交給 driver，如果中間夾雜著其他 sequence 
的 transaction，就會發生錯誤**。要解決這個問題，可以像上一節一樣，對此 sequence 賦予較高的優先權。
但是假如有其他 sequence 有更高的優先權呢？所以這種解決方法並不科學。在 UVM 中可以使用 lock 操作來解決這個問題。
所謂 lock，就是 sequence 向 sequencer 發送一個請求，這個請求與其他 sequence 發送 transaction 的請求一同被放入 sequencer 的仲裁
隊列中。當其前面的所有請求被處理完畢後，sequencer 就開始回應這個 lock 請求，此後 sequencer 會一直連續發送此 sequence 的 
transaction，直到 unlock 操作被呼叫。從效果上看，此 sequencer 的所有權並沒有被所有的 sequence 共享，而是被申請 lock 操作的 
sequence 獨佔了。一個使用 lock 操作的 sequence 為：
```
class sequence1 extends uvm_sequence #(my_transaction);
  ...
  virtual task body();
    ...
    repeat (3) begin
      `uvm_do_with(m_trans, {m_trans.pload.size < 500;})
      `uvm_info("sequence1", "send one transaction", UVM_MEDIUM)
    end
    lock();
    `uvm_info("sequence1", "locked the sequencer ", UVM_MEDIUM)
    repeat (4) begin
      `uvm_do_with(m_trans, {m_trans.pload.size < 500;})
      `uvm_info("sequence1", "send one transaction", UVM_MEDIUM)
    end
    `uvm_info("sequence1", "unlocked the sequencer ", UVM_MEDIUM)
    unlock();
    repeat (3) begin
      `uvm_do_with(m_trans, {m_trans.pload.size < 500;})
      `uvm_info("sequence1", "send one transaction", UVM_MEDIUM)
    end
    ...
  endtask
  ...
endclass
```
將此 sequence1 與前面 sequence0 在 env.i_agt.sqr 上啟動，會發現在 lock 語句前，sequence0 和 
seuquence1 交替產生 transaction；在 lock 語句後，一直傳送 sequence1 的 transaction，直到 unlock 語句被呼叫後，sequence0 和 
seuquence1 又開始交替產生 transaction。
如果兩個 sequence 都試圖使用 lock 任務來取得 sequencer 的所有權則會如何呢？答案是**先取得所有權的sequence在執行完畢後才
會將所有權交還給另外一個 sequence**。
```
class sequence0 extends uvm_sequence #(my_transaction);
  ...
  virtual task body();
    ...
    repeat (2) begin
      `uvm_do(m_trans)
      `uvm_info("sequence0", "send one transaction", UVM_MEDIUM)
    end
    lock();
    repeat (5) begin
      `uvm_do(m_trans)
      `uvm_info("sequence0", "send one transaction", UVM_MEDIUM)
    end
    unlock();
    repeat (2) begin
      `uvm_do(m_trans)
      `uvm_info("sequence0", "send one transaction", UVM_MEDIUM)
    end
    #100;
    ...
  endtask

  `uvm_object_utils(sequence0)
endclass
```
將上述 sequence0 與 sequence1 同時在 env.i_agt.sqr 上啟動，會發現 sequence0 先獲得 sequencer 的所有權，在 
unlock 函數被呼叫前，一直發送 sequence0 的 transaction。在 unlock 被呼叫後，sequence1 取得 sequencer 的所有權，之後一直發送 
sequence1 的 transaction，直到 unlock 函數被呼叫。
