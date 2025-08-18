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
## sequencer 的 grab 操作
與 lock 操作一樣，grab 操作也用於暫時擁有 sequencer 的所有權，**只是 grab 操作比 lock 操作優先權更高**。  
**lock 請求是被插入 sequencer 仲裁隊列的最後面**，等到它時，它前面的仲裁請求都已經結束了。  
**grab 請求則被放入 sequencer 仲裁隊列的最前面**，它幾乎是一發出就擁有了sequencer的所有權：
```
class sequence1 extends uvm_sequence #(my_transaction);
  ...
  virtual task body();
    ...
    repeat (3) begin
      `uvm_do_with(m_trans, {m_trans.pload.size < 500;})
      `uvm_info("sequence1", "send one transaction", UVM_MEDIUM)
    end
    grab();
    `uvm_info("sequence1", "grab the sequencer ", UVM_MEDIUM)
    repeat (4) begin
      `uvm_do_with(m_trans, {m_trans.pload.size < 500;})
      `uvm_info("sequence1", "send one transaction", UVM_MEDIUM)
    end
    `uvm_info("sequence1", "ungrab the sequencer ", UVM_MEDIUM)
    ungrab();
    repeat (3) begin
      `uvm_do_with(m_trans, {m_trans.pload.size < 500;})
      `uvm_info("sequence1", "send one transaction", UVM_MEDIUM)
    end
    ...
  endtask

  `uvm_object_utils(sequence1)
endclass
```
如果兩個 sequence 同時試圖使用 grab 任務來取得 sequencer 的所有權將會如何呢？這種情況與兩個 sequence 同時試圖呼叫 lock 函數
一樣，在先取得所有權的 sequence 執行完畢後才會將所有權交還給另外一個試圖所有權的 sequence。
如果一個 sequence 在使用 grab 任務取得 sequencer 的所有權前，另一個 sequence 已經使用 lock 任務取得了 sequencer 的所有權則
會如何呢？答案是 grab 任務會一直等待 lock 的釋放。 **grab 任務還是比較講文明的，雖然它會插隊，但是絕對不會打斷別人正在進行的
事情**。
## sequence 的有效性
當有多個 sequence 同時在一個 sequencer 上啟動時，所有的 sequence 都參與仲裁，根據演算法決定哪個 sequence 發送 transaction。仲
裁算法是由 sequencer 決定的，sequence 除了可以在優先權上設定外，對仲裁的結果無能為力。
透過 lock 任務和 grab 任務，sequence 可以獨佔 sequencer，強行使 sequencer 發送自己產生的 transaction。同樣的，UVM 也提供措
施使 sequence 可以在一定時間內不參與仲裁，即令此 sequence 失效。
sequencer 在仲裁時，會查看 sequence 的 is_relevant 函數的回傳結果。如果為 1，說明此 sequence 有效，否則無效。因此可以透過
重載 is_relevant 函數來使 sequence 失效：
```
class sequence0 extends uvm_sequence #(my_transaction);
  my_transaction m_trans;
  int num;
  bit has_delayed;
  ...
  // 覆寫 is_relevant
  virtual function bit is_relevant();
    if ((num >= 3) && (!has_delayed)) return 0;
    else return 1;
  endfunction

  virtual task body();
    ...
    fork
      repeat (10) begin
        num++;
        `uvm_do(m_trans)
        `uvm_info("sequence0", "send one transaction", UVM_MEDIUM)
      end

      while (1) begin
        if (!has_delayed) begin
          if (num >= 3) begin
            `uvm_info("sequence0", "begin to delay", UVM_MEDIUM)
            #500000;
            has_delayed = 1'b1;
            `uvm_info("sequence0", "end delay", UVM_MEDIUM)
            break;
          end else
            #1000;
        end
      end
    join
    ...
  endtask
  ...
endclass
```
這個 sequence 在發送了 3 個 transaction 後開始變成無效，延遲 500000 時間單位後又開始有效。將此 sequence 與 
sequence1 同時啟動，會發現在失效前 sequence0 和 sequence1 交替發送 transaction；而在失效的 500000 時間單位內，只有 sequence1 發
送 transaction；當 sequence0 重新變有效後，sequence0 和 sequence1 又開始交替發送 transaction。從某種程度上來說，is_relevant 與 grab
 任務和 lock 任務是完全相反的。透過設定 is_relevant，可以讓 sequence 主動放棄 sequencer 的使用權，而 grab 任務和 lock 任務則強佔 sequencer 的所有權。除了 is_relevant 外，sequence 中還有一個任務 wait_for_relevant 也與 sequence 的有效性有關：
```
class sequence0 extends uvm_sequence #(my_transaction);
  ...

  virtual function bit is_relevant();
    if ((num >= 3) && (!has_delayed)) return 0;
    else return 1;
  endfunction

  virtual task wait_for_relevant();
    #10000;
    has_delayed = 1;
  endtask

  virtual task body();
    ...
    repeat (10) begin
      num++;
      `uvm_do(m_trans)
      `uvm_info("sequence0", "send one transaction", UVM_MEDIUM)
    end
    ...
  endtask

  ...
endclass
```
當 sequencer 發現在其上啟動的所有 sequence 都無效時，此時會呼叫 wait_for_relevant 並等待 sequence 變有效。當此 sequence 與 sequence1 同時啟動，並發送了 3 個 transaction 後，sequence0 變成無效。此後 sequencer 一直發送 sequence1 的 
transaction，直到全部的 transaction 都寄完畢。此時，sequencer 發現 sequence0 無效，會呼叫其 wait_for_relevant。換言之， 
sequence0 失效是自己控制的，但是重新變成有效卻是受其他 sequence 的控制。如果其他 sequence 永遠不結束，那麼 sequence0 將永遠
遠處於失效狀態。這裡與程式碼清單6-19範例的差別是，程式碼清單6-19範例中 sequence0 並不是等待著 sequence1 的 transaction 全部發
送完畢，而是自己主動控制自己何時有效何時無效。
在 wait_for_relevant 中，必須將使 sequence 無效的條件清除。在程式碼清單6-20中，假如 wait_for_relevant 只是如下定義：
```
virtual task wait_for_relevant();
  #10000;
endtask
```
那麼當 wait_for_relevant 回傳後，sequencer 會繼續呼叫 sequence0 的 is_relevant，發現依然是無效狀態，則繼續呼叫
wait_for_relevant。系統會處於死循環的狀態。
在代碼清單6-19的例子中，透過控制延時（500000）單位時間來使 sequence0 重新變得有效。假如在這段時間內，sequence1 的
 transaction 發送完畢後，而 sequence0 中又沒有重載 wait_for_relevant 任務，那麼將會給出如下錯誤提示：
```
UVM_FATAL @ 1166700: uvm_test_top.env.i_agt.sqr@@seq0 [RELMSM] is_relevant()was implemented without defining
```
因此，is_relevant 與 wait_for_relevant 一般應成對重載，不能只重載其中的一個。程式碼清單6-19的例子中沒有重載 
wait_for_relevant，是因為巧妙地設定了延時，可以保證不會呼叫到 wait_for_relevant。讀者在使用時應該重載 wait_for_relevant 這個
任務。
# sequence 相關巨集及其實現
## uvm_do 系列宏
uvm_do 系列宏主要有以下 8 個：
```
`uvm_do(SEQ_OR_ITEM)
`uvm_do_pri(SEQ_OR_ITEM, PRIORITY)
`uvm_do_with(SEQ_OR_ITEM, CONSTRAINTS)
`uvm_do_pri_with(SEQ_OR_ITEM, PRIORITY, CONSTRAINTS)
`uvm_do_on(SEQ_OR_ITEM, SEQR)
`uvm_do_on_pri(SEQ_OR_ITEM, SEQR, PRIORITY)
`uvm_do_on_with(SEQ_OR_ITEM, SEQR, CONSTRAINTS)
`uvm_do_on_pri_with(SEQ_OR_ITEM, SEQR, PRIORITY, CONSTRAINTS)
```
其中 uvm_do、uvm_do_with、uvm_do_pri、uvm_do_pri_with 在前面已經提到過了，這裡只介紹另外 4 個。
## uvm_do_on 
* 用於明確指定使用哪個 sequencer 發送此 transaction
  * 第一個參數是 transaction 的指針
  * 第二個參數是 sequencer 的指標
* 當在 sequence 中使用 uvm_do 等巨集時，其預設的 sequencer 就是此 sequence 啟動時為其指定的 sequencer，sequence 將這個 sequencer 的指標放在其成員變數 m_sequencer 中。事實上，uvm_do 等價於：
```
`uvm_do_on(tr, this.m_sequencer)  // 此 transaction 是在當前 sequencer 發送
```
這裡看起來指定使用哪個 sequencer 似乎並沒有用，它的真正作用要在6.5節 virtual sequence 中體現。
## uvm_do_on_pri
  * 第一個參數是 transaction 的指針
  * 第二個是 sequencer 的指針
  * 第三個是優先權：
```
`uvm_do_on(tr, this, 100)
```
## uvm_do_on_with
 * 第一個參數是 transaction 的指針
 * 第二個是 sequencer 的指針
 * 第三個是約束：
```
`uvm_do_on_with(tr, this, {tr.pload.size == 100;})
```
## uvm_do_on_pri_with
* 所有 uvm_do 巨集中參數最多的一個
  * 第一個參數是 transaction 的指針
  * 第二個是 sequencer 的指針
  * 第三個是優先級
  * 第四個是約束：
```
`uvm_do_on_pri_with(tr, this, 100, {tr.pload.size == 100;})
```
uvm_do 系列的其他七個宏其實都是用 uvm_do_on_pri_with 巨集來實現的。如 uvm_do 宏：
```
`define uvm_do(SEQ_OR_ITEM) \
    `uvm_do_on_pri_with(SEQ_OR_ITEM, m_sequencer, -1, {})
```
## uvm_create 與 uvm_send
除了使用 uvm_do 巨集產生 transaction，還可以使用 uvm_create 巨集與 uvm_send 巨集來產生：
```
class case0_sequence extends uvm_sequence #(my_transaction);
...
  virtual task body();
    int num = 0;
    int p_sz;
...
    repeat (10) begin
      num++;
      `uvm_create(m_trans)
      assert(m_trans.randomize());
      p_sz = m_trans.pload.size();
      {m_trans.pload[p_sz - 4],
       m_trans.pload[p_sz - 3],
       m_trans.pload[p_sz - 2],
       m_trans.pload[p_sz - 1]} = num;
      `uvm_send(m_trans)
    end
...
  endtask
...
endclass
```
**uvm_create 巨集的作用是實例化 transaction**。當一個 transaction 被實例化後，可以對其做更多的處理，**處理完畢後使用 uvm_send 宏送出去**。這種使用方式比 uvm_do 系列巨集更靈活。如在上例中，**就將 pload 的最後 4 個 byte 替換為此 transaction 的序號**。
事實上，在上述的程式碼中，也完全可以不使用 uvm_create 宏，而直接呼叫 new 進行實例化：
```
virtual task body();
  …
    m_trans = new("m_trans");
    assert(m_trans.randomize());
    p_sz = m_trans.pload.size();
    {m_trans.pload[p_sz - 4],
    m_trans.pload[p_sz - 3],
    m_trans.pload[p_sz - 2],
    m_trans.pload[p_sz - 1]}
    = num;
    `uvm_send(m_trans)
  …
endtask
```
除了 uvm_send 外，還有 uvm_send_pri 宏，它的作用是在將 transaction 交給 sequencer 時設定優先權：
```
virtual task body();
  …
  m_trans = new("m_trans");
  assert(m_trans.randomize());
  p_sz = m_trans.pload.size();
  {m_trans.pload[p_sz - 4],
  m_trans.pload[p_sz - 3],
  m_trans.pload[p_sz - 2],
  m_trans.pload[p_sz - 1]}
  = num;
  `uvm_send_pri(m_trans, 200)
  …
endtask
```
## uvm_rand_send 系列宏
uvm_rand_send 系列宏有以下幾個：
```
`uvm_rand_send(SEQ_OR_ITEM)
`uvm_rand_send_pri(SEQ_OR_ITEM, PRIORITY)
`uvm_rand_send_with(SEQ_OR_ITEM, CONSTRAINTS)
`uvm_rand_send_pri_with(SEQ_OR_ITEM, PRIORITY, CONSTRAINTS)
```
## uvm_rand_send
uvm_rand_send 巨集與 uvm_send 巨集類似，**唯一的差別是它會對 transaction 進行隨機化**。**這個巨集使用的前提是 transaction 已經被分配了空間**，換言之，即已經實例化了：
```
m_trans = new("m_trans");
`uvm_rand_send(m_trans)
```
## uvm_rand_send_pri
uvm_rand_send_pri 巨集用於指定 transaction 的優先權。它有兩個參數，第一個是transaction的指針，第二個是優先權：
```
m_trans = new("m_trans");
`uvm_rand_send_pri(m_trans, 100)
```
## uvm_rand_send_with
uvm_rand_send_with 宏，用於指定使用隨機化時的約束，它有兩個參數，第一個是 transaction 的指針，第二個是約束：
```
m_trans = new("m_trans");
`uvm_rand_send_with(m_trans, {m_trans.pload.size == 100;})
```
## uvm_rand_send_pri_with
uvm_rand_send_pri_with 宏，用於指定優先權和約束，它有三個參數，第一個是 transaction 的指針，第二個是優先權，第三個
是約束：
```
m_trans = new("m_trans");
`uvm_rand_send_pri_with(m_trans, 100, {m_trans.pload.size == 100;})
```
uvm_rand_send 系列巨集及 uvm_send 系列巨集的意義主要在於，如果一個 transaction 佔用的記憶體比較大，那麼很可能希望前後兩次發送的 transaction 都使用同一塊內存，只是其中的內容可以不同，這樣比較節省內存。
# start_item 與 finish_item
不使用巨集產生 transaction 的方式要依賴兩個任務：start_item 和 finish_item。在使用這兩個任務前，必須先實例化 transaction
後才可以呼叫這兩個任務：
```
tr = new("tr");
start_item(tr);
finish_item(tr);
```
完整使用如上兩個任務所建構的一個 sequence 如下：
```
virtual task body();
  repeat(10) begin
    tr = new("tr");
    start_item(tr);
    finish_item(tr);
  end
endtask
```
上述程式碼中並沒有對 tr 進行隨機化。可以在 transaction 實例化後、finish_item 呼叫前進行隨機化：
```
class case0_sequence extends uvm_sequence #(my_transaction);
...
  virtual task body();
...
    repeat (10) begin
      tr = new("tr");
      assert(tr.randomize() with {tr.pload.size == 200;});
      start_item(tr);
      finish_item(tr);
    end
...
  endtask
...
endclass
```
上述 assert 語句也可以放在 start_item 之後、finish_item 之前。 uvm_do 系列宏其實是將下述動作封裝在了一個巨集中：
```
virtual task body();
  …
  tr = new("tr");
  start_item(tr);
  assert(tr.randomize() with {tr.pload.size() == 200;});
  finish_item(tr);
  …
endtask
```
如果要指定 transaction 的優先權，那麼要在呼叫 start_item 和 finish_item 時都要加入優先權參數：
```
virtual task body();
  …
  start_item(tr, 100);
  finish_item(tr, 100);
  …
endtask
```
如果不指定優先權參數，預設的優先權為 -1
## pre_do、mid_do 與 post_do
uvm_do 巨集封裝了從 transaction 實例化到傳送的一系列操作，封裝的越多，則其彈性越差。為了增加 uvm_do 系列巨集的功能，
UVM 提供了三個介面：pre_do、mid_do與post_do。
* pre_do 是一個任務，在 start_item 中被調用，它是 start_item 返回前執行的最後一行程式碼，在它執行完畢後才對 transaction 進行隨機化
* mid_do 是一個函數，位於 finish_item 的最開始。執行完此函數後，finish_item 才進行其他操作。
* post_do 也是一個函數，也位於 finish_item 中，它是 finish_item 返回前執行的最後一行程式碼。它們的執行順序大致為：
```
sequencer.wait_for_grant(prior) (task) \ start_item \
parent_seq.pre_do(1) (task)            /             \
                                                      `uvm_do* macros
parent_seq.mid_do(item) (func)         \              /
sequencer.send_request(item) (func)     \finish_item /
sequencer.wait_for_item_done() (task)   /
parent_seq.post_do(item) (func)        /
```
wait_for_grant、send_request 及 wait_for_item_done 都是 UVM 內部的一些介面。這三個介面函數/任務的使用範例如下：
```
class case0_sequence extends uvm_sequence #(my_transaction);
  my_transaction m_trans;
  int num;
...
  virtual task pre_do(bit is_item);
    #100;
    `uvm_info("sequence0", "this is pre_do", UVM_MEDIUM)
  endtask

  virtual function void mid_do(uvm_sequence_item this_item);
    my_transaction tr;
    int p_sz;
    `uvm_info("sequence0", "this is mid_do", UVM_MEDIUM)
    void'($cast(tr, this_item));
    p_sz = tr.pload.size();
    {tr.pload[p_sz - 4],
     tr.pload[p_sz - 3],
     tr.pload[p_sz - 2],
     tr.pload[p_sz - 1]} = num;
    tr.crc = tr.calc_crc();
    tr.print();
  endfunction

  virtual function void post_do(uvm_sequence_item this_item);
    `uvm_info("sequence0", "this is post_do", UVM_MEDIUM)
  endfunction

  virtual task body();
...
    repeat (10) begin
      num++;
      `uvm_do(m_trans)
    end
...
  endtask
...
endclass
```
pre_do 有一個參數，此參數用來表示 uvm_do 宏是在對一個 transaction 還是在對一個 sequence 進行操作，關於這一點請參考6.4.1
節。 mid_do 和 post_do 的兩個參數是正在操作的 sequence 或 item 的指針，但其型別是 uvm_sequence_item 型別。透過 cast 可以轉換成目標類型（範例中為my_transaction）。
## 嵌套的 sequence
假設一個產生 CRC 錯誤包的 sequence 如下：
```
class crc_seq extends uvm_sequence#(my_transaction);
…
  virtual task body();
    my_transaction tr;
    `uvm_do_with(tr, {tr.crc_err == 1; tr.dmac == 48'h980F;})
  endtask
endclass
```
另外一個產生長包的 sequence 如下：
```
class long_seq extends uvm_sequence#(my_transaction);
…
  virtual task body();
    my_transaction tr;
    `uvm_do_with(tr, {tr.crc_err == 0; tr.pload.size() == 1500; tr.dmac == 48'hF675;})
  endtask
endclass
```
現在要寫一個新的 sequence，它可以交替產生上面的兩種包。那麼在新的 sequence 裡面可以這樣寫：
```
class case0_sequence extends uvm_sequence #(my_transaction);
  virtual task body();
  my_transaction tr;
  repeat (10) begin
    `uvm_do_with(tr, {tr.crc_err == 1; tr.dmac == 48'h980F;})
    `uvm_do_with(tr, {tr.crc_err == 0; tr.pload.size() == 1500; tr.dmac == 48'hF675;})
  end
  endtask
endclass
```
似乎這樣寫起來顯得特別麻煩。產生的兩種不同的包中，第一個約束條件有兩個，第二個約束條件有三個。但是假如約束條
件有十個呢？如果整個驗證平台中有 30 個測試案例都用到這樣的兩種包，那就要在這 30 個測試案例的 sequence 中加入這些程式碼，
這是一件相當恐怖的事情，而且特別容易出錯。既然已經定義好 crc_seq 和 long_seq，那麼有沒有簡單的方法呢？答案是肯定的。
在一個 sequence 的 body 中，除了可以使用 uvm_do 巨集產生 transaction 外，其實還可以啟動其他的 sequence，也就是一個 sequence 內啟動另外一個 sequence，這就是嵌套的 sequence：
```
class case0_sequence extends uvm_sequence #(my_transaction);
…
  virtual task body();
    crc_seq cseq;
    long_seq lseq;
    …
    repeat (10) begin
      cseq = new("cseq");
      cseq.start(m_sequencer);
      lseq = new("lseq");
      lseq.start(m_sequencer);
    end
  …
  endtask
…
endclass
```
直接在新的 sequence 的 body 中呼叫定義好的 sequence，從而實作 sequence 的重用。這個功能是非常強大的。在上面程式碼中， 
m_sequencer 是 case0_sequence 啟動後所使用的 sequencer 的指標。但通常來說並不用這麼麻煩，可以使用 uvm_do 宏來完成這些事情：
```
class case0_sequence extends uvm_sequence #(my_transaction);
…
  virtual task body();
    crc_seq cseq;
    long_seq lseq;
    …
    repeat (10) begin
      `uvm_do(cseq)
      `uvm_do(lseq)
    end
    …
  endtask
…
endclass
```
uvm_do 系列巨集中，其第一個參數除了可以是 transaction 的指標外，還可以是某個 sequence 的指標。當第一個參數是 transaction
時，它如6.3.4節程式碼清單6-39所示，呼叫 start_item 和 finish_item；當第一個參數是 sequence 時，它呼叫此 sequence 的 start 任務。
除了 uvm_do 宏外，前面介紹的 uvm_send 宏、uvm_rand_send 宏、uvm_create 宏，其第一個參數都可以是 sequence 的指標。唯一
例外的是 start_item 與 finish_item，這兩個任務的參數必須是 transaction 的指標。
## 在 sequence 中使用 rand 類型變數
在 transaction 的定義中，通常會使用 rand 來對變數進行修飾，說明在呼叫 randomize 時要對此欄位進行隨機化。其實在 sequence 中
也可以使用 rand 修飾因子。有如下的 sequence，它有成員變數 ldmac：
```
class long_seq extends uvm_sequence#(my_transaction);
  rand bit[47:0] ldmac;
  …
  virtual task body();
    my_transaction tr;
    `uvm_do_with(tr, {tr.crc_err == 0;
    tr.pload.size() == 1500;
    tr.dmac == ldmac;})
    tr.print();
  endtask
endclass
```
這個 sequence 可以當作底層的 sequence 被頂層的 sequence 呼叫：
```
class case0_sequence extends uvm_sequence #(my_transaction);
  …
  virtual task body();
    long_seq lseq;
    …
    repeat (10) begin
    `uvm_do_with(lseq, {lseq.ldmac == 48'hFFFF;})
    end
    …
  endtask
  …
endclass
```
sequence 裡可以加入任意多的 rand 修飾符，用以規範它所產生的 transaction。 sequence 與 transaction 都可以呼叫 randomize 進行隨機化，都可以有 rand 修飾符的成員變量，從某種程度上來說，二者的界線比較模糊。這也就是為什麼 uvm_do 系列宏可以接受 
sequence 作為其參數的原因。
在 sequence 中定義 rand 類型變數時，要注意變數的命名。很多人習慣於變數的名字和 transaction 中對應欄位的名字一致：
```
class long_seq extends uvm_sequence#(my_transaction);
  rand bit[47:0] dmac;
  …
  virtual task body();
    my_transaction tr;
    `uvm_do_with(tr, {tr.crc_err == 0;
    tr.pload.size() == 1500;
    tr.dmac == dmac;})
    tr.print();
  endtask
endclass
```
在 case0_sequence 中啟動上述 sequence，並將 dmac 位址約束為 48’hFFFF，此時將會發現產生的 transaction 的 dmac 並不是 
48‘hFFFF，而是一個隨機值！這是因為，執行到上述程式碼的第15行時，編譯器會先去 my_transaction 找 dmac，如果找到了，
就不再繼續尋找。換言之，止述代號第13到第15行等價於：
```
`uvm_do_with(tr, {tr.crc_err == 0;
tr.pload.size() == 1500;
tr.dmac == tr.dmac;})
```
long_seq 中的 dmac 並沒有起到作用。所以，在 sequence 中定義 rand 類型變數以傳遞約束到產生的 transaction 時，變數的名字一定要與 transaction 中對應欄位的名字不同。
## transaction 類型的匹配
一個 sequencer 只能產生一種類型的 transaction，一個 sequence 如果要想在此 sequencer 上啟動，那麼其所產生的 transaction 的類型必須是這種 transaction 或是派生自這種 transaction。
如果一個 sequence 中產生的 transaction 的類型不是此種 transaction，那麼將會報錯：
```
class case0_sequence extends uvm_sequence #(my_transaction);
  your_transaction y_trans;
  virtual task body();
    repeat (10) begin
      `uvm_do(y_trans)
    end
  endtask
endclass
```
**巢狀 sequence 的前提是，在套裡面的所有 sequence 產生的 transaction 都可以被同一個 sequencer 所接受**。
那麼有沒有辦法將兩個截然不同的 transaction 交給同一個 sequencer 呢？可以，只是需要將 sequencer 和 driver 能夠接受的資料類
型設定為 uvm_sequence_item：
```
class my_sequencer extends uvm_sequencer #(uvm_sequence_item);
class my_driver extends uvm_driver#(uvm_sequence_item);
```
在 sequence 中可以交替傳送 my_transaction 和 your_transaction：
```
class case0_sequence extends uvm_sequence;
  my_transaction m_trans;
  your_transaction y_trans;
  …
  virtual task body();
  …
    repeat (10) begin
    `uvm_do(m_trans)
    `uvm_do(y_trans)
    end
  …
  endtask
  
  `uvm_object_utils(case0_sequence)
endclass
```
這樣帶來的問題是，由於 driver 中接收的資料類型是 uvm_sequence_item，如果它要使用 my_transaction 或 your_transaction 中的
成員變量，必須使用 cast 轉換：
```
task my_driver::main_phase(uvm_phase phase);
  my_transaction m_tr;
  your_transaction y_tr;
...
  while (1) begin
    seq_item_port.get_next_item(req);
    if ($cast(m_tr, req)) begin
      drive_my_transaction(m_tr);
      `uvm_info("driver", "receive a transaction whose type is my_transaction", UVM_MEDIUM)
    end
    else if ($cast(y_tr, req)) begin
      drive_your_transaction(y_tr);
      `uvm_info("driver", "receive a transaction whose type is your_transaction", UVM_MEDIUM)
    end
    else begin
      `uvm_error("driver", "receive a transaction whose type is unknown")
    end
    seq_item_port.item_done();
  end
endtask
```
## p_sequencer 的使用
考慮下列一種情況，在 sequencer 中存在以下成員變數：
```
class my_sequencer extends uvm_sequencer #(my_transaction);
  bit [47:0] dmac;
  bit [47:0] smac;
......
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    void'(uvm_config_db#(bit[47:0])::get(this, "", "dmac", dmac));
    void'(uvm_config_db#(bit[47:0])::get(this, "", "smac", smac));
  endfunction

  `uvm_component_utils(my_sequencer)
endclass
```
在其 build_phase 中，使用 config_db：：get 得到這兩個成員變數的值。之後 sequence 在發送 transaction 時，必須將目的位址設定
為 dmac，來源位址設定為 smac。現在的問題是，如何在 sequence 的 body 中得到這兩個變數的值呢？
在6.4.1節介紹巢狀的 sequence 時，引入了 m_sequencer 這個屬於每個 sequence 的成員變量，但如果直接使用 m_sequencer 得
到這兩個變數的值：
```
virtual task body();
…
  repeat (10) begin
    `uvm_do_with(m_trans, {m_trans.dmac == m_sequencer.dmac; m_trans.smac == m_sequencer.smac;})
  end
…
endtask
```
如上寫法會造成編譯錯誤。其根源在於 m_sequencer 是 uvm_sequencer_base（uvm_sequencer 的基底類別）類型的，而不是 
my_sequencer 類型的。 m_sequencer 的原型為：
```
protected uvm_sequencer_base m_sequencer;
```
但由於 case0_sequence 在 my_sequencer 上啟動，其中的 m_sequencer 本質上是 my_sequencer 類型的，所以可以在 my_sequence 
中透過 cast 轉換將 m_sequencer 轉換成 my_sequencer 類型，並引用其中的 dmac 和 smac：
```
virtual task body();
  my_sequencer x_sequencer;
…
  $cast(x_sequencer, m_sequencer);
  repeat (10) begin
   `uvm_do_with(m_trans, {m_trans.dmac == x_sequencer.dmac; m_trans.smac == x_sequencer.smac;})
  end
…
endtask
```
上述過程稍顯麻煩。在實際的驗證平台中，用到 sequencer 中成員變數的情況非常多。 UVM 考慮到這種情況，內建了一個巨集：
uvm_declare_p_sequencer（SEQUENCER）。這個巨集的本質是宣告了一個 SEQUENCER 類型的成員變量，如在定義 sequence 時，使
用此巨集聲明 sequencer 的類型：
```
class case0_sequence extends uvm_sequence #(my_transaction);
  my_transaction m_trans;
  `uvm_object_utils(case0_sequence)
  `uvm_declare_p_sequencer(my_sequencer)
…
endclass
```
則相當於宣告如下的成員變數：
```
class case0_sequence extends uvm_sequence #(my_transaction);
  my_sequencer p_sequencer;
  …
endclass
```
UVM 之後會自動將 m_sequencer 透過 cast 轉換成 p_sequencer。這個過程在 pre_body() 之前就完成了。因此在 sequence 中可以
直接使用成員變數 p_sequencer 來引用 dmac 和 smac：
```
class case0_sequence extends uvm_sequence #(my_transaction);
…
  virtual task body();
  …
    repeat (10) begin
    `uvm_do_with(m_trans, {m_trans.dmac == p_sequencer.dmac; m_trans.smac == p_sequencer.smac;})
    end
  …
  endtask

endclass
```
## sequence 的派生與繼承
sequence 作為一個類，是可以從其中派生其他 sequence 的：
```
class base_sequence extends uvm_sequence #(my_transaction);
  `uvm_object_utils(base_sequence)
  `uvm_declare_p_sequencer(my_sequencer)

  function new(string name = "base_sequence");
    super.new(name);
  endfunction

  // Define some common functions and tasks
endclass

class case0_sequence extends base_sequence;
  // Specific implementation for case0
endclass
```
由於在同一個專案中各 sequence 都是類似的，所以可以將許多公用的函數或任務寫在 base sequence 中，其他 sequence 都從此 
sequence 派生。
普通的 sequence 這樣使用沒有任何問題，但對於那些使用了 uvm_declare_p_sequence 聲明 p_sequencer 的 base sequence，在派生
的 sequence 中是否也要呼叫此巨集宣告 p_sequencer？這個問題的答案是否定的，因為 uvm_declare_p_sequence 的實質是在 base sequence 
中宣告了一個成員變數 p_sequencer。當其他的 sequence 從其派生時，p_sequencer 仍然是新的 sequence 的成員變量，所以無
須再聲明一次了。
當然了，如果再聲明一次，系統也不會報錯：
```
class base_sequence extends uvm_sequence #(my_transaction);
  `uvm_object_utils(base_sequence)
  `uvm_declare_p_sequencer(my_sequencer)
  …
endclass
class case0_sequence extends base_sequence;
  `uvm_object_utils(case0_sequence)
  `uvm_declare_p_sequencer(my_sequencer)
…
endclass
```
雖然這相當於連續宣告了兩個成員變數 p_sequencer，但由於這兩個成員變數一個是屬於父類別的，一個是屬於子類別的，所以
並不會出錯。
## virtual sequence 的使用
## 帶雙路輸入輸出埠的 DUT
在本書先前所有的例子中，所使用的 DUT 幾乎都是基於2.2.1節中所示的最簡單的 DUT。為了說明 virtual sequence，本節引入附
錄B的代碼B-1所示的 DUT。
這個 DUT 相當於在2.2.1節所示的 DUT 的基礎上增加了一組資料口，這組新的資料口與原先的資料口功能完全一樣。新的數據
連接埠增加後，由於這組新的資料埠與原先的一模一樣，所以可以在 test 中再額外實例化一個 my_env：
```
class base_test extends uvm_test;
  my_env env0;
  my_env env1;
…
endclass

function void base_test::build_phase(uvm_phase phase);
  super.build_phase(phase);
  env0 = my_env::type_id::create("env0", this);
  env1 = my_env::type_id::create("env1", this);
endfunction
```
在 top_tb 中做相應更改，多增加一組 my_if，並透過 config_db 將其設定為新的 env 中的 driver 和 monitor：
```
module top_tb;

  // Interface instance connections
  my_if input_if0(clk, rst_n);
  my_if input_if1(clk, rst_n);
  my_if output_if0(clk, rst_n);
  my_if output_if1(clk, rst_n);

  // DUT instantiation
  dut my_dut(
    .clk(clk),
    .rst_n(rst_n),
    .rxd0(input_if0.data),
    .rx_dv0(input_if0.valid),
    .rxd1(input_if1.data),
    .rx_dv1(input_if1.valid),
    .txd0(output_if0.data),
    .tx_en0(output_if0.valid),
    .txd1(output_if1.data),
    .tx_en1(output_if1.valid)
  );

  initial begin
    uvm_config_db#(virtual my_if)::set(null, "uvm_test_top.env0.i_agt.drv", "vif", input_if0);
    uvm_config_db#(virtual my_if)::set(null, "uvm_test_top.env0.i_agt.mon", "vif", input_if0);
    uvm_config_db#(virtual my_if)::set(null, "uvm_test_top.env0.o_agt.mon", "vif", output_if0);

    uvm_config_db#(virtual my_if)::set(null, "uvm_test_top.env1.i_agt.drv", "vif", input_if1);
    uvm_config_db#(virtual my_if)::set(null, "uvm_test_top.env1.i_agt.mon", "vif", input_if1);
    uvm_config_db#(virtual my_if)::set(null, "uvm_test_top.env1.o_agt.mon", "vif", output_if1);
  end

endmodule
```
透過在測試用例中設定兩個 default sequence，可以分別向兩個資料連接埠施加激勵：
```
function void my_case0::build_phase(uvm_phase phase);
  super.build_phase(phase);
  
  uvm_config_db#(uvm_object_wrapper)::set(this, "env0.i_agt.sqr.main_phase", "default_sequence", case0_sequence::type_id::get());
  uvm_config_db#(uvm_object_wrapper)::set(this, "env1.i_agt.sqr.main_phase", "default_sequence", case0_sequence::type_id::get());
endfunction
```
## sequence 之間的簡單同步
在這個新的驗證平台中有兩個 driver，它們原本是完全等價的，但是出於某些原因的考慮，如 DUT 要求 driver0 必須先發送一個
最大長度的包，在此基礎上 driver1 才可以發送包。這是一個 sequence 之間同步的過程，一個很自然的想法是，將這個同步的過程
使用一個全域的事件來完成：
```
文件：src/ch6/section6.5/6.5.2/my_case0.sv
event send_over; // global event
class drv0_seq extends uvm_sequence #(my_transaction);
...
  virtual task body();
...
    `uvm_do_with(m_trans, {m_trans.pload.size == 1500;})
    ->send_over; // trigger event

    repeat (10) begin
      `uvm_do(m_trans)
      `uvm_info("drv0_seq", "send one transaction", UVM_MEDIUM)
    end
...
  endtask
endclass

class drv1_seq extends uvm_sequence #(my_transaction);
...
  virtual task body();
    @send_over; // wait for event

    repeat (10) begin
      `uvm_do(m_trans)
      `uvm_info("drv1_seq", "send one transaction", UVM_MEDIUM)
    end
...
  endtask
endclass
```
之後，透過 uvm_config_db 的方式分別將這兩個 sequence 作為 env0.i_agt.sqr 和 env1.i_agt.sqr 的 default_sequence：
```
function void my_case0::build_phase(uvm_phase phase);
  super.build_phase(phase);

  uvm_config_db#(uvm_object_wrapper)::set(this,
    "env0.i_agt.sqr.main_phase",
    "default_sequence",
    drv0_seq::type_id::get());

  uvm_config_db#(uvm_object_wrapper)::set(this,
    "env1.i_agt.sqr.main_phase",
    "default_sequence",
    drv1_seq::type_id::get());
endfunction
```
當進入 main_phase 時，這兩個 sequence 會同步啟動，但由於 drv1_seq 要等待 send_over 事件的到來，所以它並不會馬上產生
transaction，而 drv0_seq 則會直接產生 transaction。當 drv0_se q發送完一個最長套件後，send_over 事件被觸發，於 drv1_seq 開始產生
transaction。
## sequence 之間的複雜同步
上節解決同步的方法看起來非常簡單、實用。不過這裡有兩個問題，
第一個問題是使用了一個全域的事件 send_over。全域變數對於初寫程式碼的人來說是非常受歡迎的，但是幾乎所有的老師及書本中都會這麼說：除非有必要，否則盡量不要使用全域變
量。使用全域變數的主要問題即它是全域可見的，本來只是打算在 drv0_seq 和 drv1_seq 中使用這個全域變量，但假如其他的某個 
sequence 也不小心使用了這個全域變量，在 drv0_seq 觸發 send_over 事件之前，這個 sequence 已經觸發了此事件，這是不允許的。所
以應該盡量避免全域變數的使用。
第二個問題是上面只是實作了一次同步，如果有多次同步怎麼辦？如 sequence A 要先執行，之後是 B，B 執行後才能是 C，C
執行後才能是 D，D 執行後才能是 E。這仍然可以使用上面的全局方法解決，只是這會顯得相當笨拙。
實現 sequence 之間同步的最好的方式就是使用 virtual sequence。從字面上理解，即虛擬的 sequence。虛擬的意思就是它根本就
不發送 transaction，它只是控制其他的 sequence，起統一調度的作用。
如圖6-1所示，為了使用 virtual sequence，一般需要一個 virtual sequencer。 virtual sequencer 裡面包含指向其他真實 sequencer 的指
針：
```
class my_vsqr extends uvm_sequencer;

  my_sequencer p_sqr0;
  my_sequencer p_sqr1;
…
endclass
```
在 base_test 中，實例化 vsqr，並將對應的 sequencer 賦值給 vsqr 中的 sequencer 的指標：
```
class base_test extends uvm_test;

  my_env env0;
  my_env env1;
  my_vsqr v_sqr;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env0 = my_env::type_id::create("env0", this);
    env1 = my_env::type_id::create("env1", this);
    v_sqr = my_vsqr::type_id::create("v_sqr", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    v_sqr.p_sqr0 = env0.i_agt.sqr;
    v_sqr.p_sqr1 = env1.i_agt.sqr;
  endfunction

endclass
```
<img width="1185" height="792" alt="image" src="https://github.com/user-attachments/assets/f0118594-ca21-496e-859f-138b61445d9c" />
在 virtual sequene 中則可以使用 uvm_do_on 系列巨集來傳送 transaction：
```
class case0_vseq extends uvm_sequence;
  `uvm_object_utils(case0_vseq)
  `uvm_declare_p_sequencer(my_vsqr)
  …
  virtual task body();
    my_transaction tr;
    drv0_seq seq0;
    drv1_seq seq1;
    …
    `uvm_do_on_with(tr, p_sequencer.p_sqr0, {tr.pload.size == 1500;})
    `uvm_info("vseq", "send one longest packet on p_sequencer.p_sqr0", UVM_MEDIUM)
    fork
      `uvm_do_on(seq0, p_sequencer.p_sqr0);
      `uvm_do_on(seq1, p_sequencer.p_sqr1);
    join
  …
  endtask
endclass
```
在使用 uvm_do_on 巨集的情況下，雖然 seq0 是在 case0_vseq 中啟動，但它最終會交給 p_sequencer.p_sqr0，也即 env0.i_agt.sqr
而不是 v_sqr。這就是 virtual sequence 和 virtual sequencer 中 virtual 的來源。**它們各自並不產生 transaction，而只是控制其他的
sequence 為對應的 sequencer 產生 transaction**。virtual sequence 和 virtual sequencer 只是扮演一個調度的角色。由於根本不直接產生 
transaction，所以 virtual sequence 和 virtual sequencer 在定義時根本無需指明要傳送的 transaction 資料類型。
如果不使用 uvm_do_on 宏，那麼也可以手動啟動 sequence，其效果完全一樣。手工啟動 sequence 的一個優點是可以向其中傳遞
一些值：
```
class read_file_seq extends uvm_sequence #(my_transaction);
  my_transaction m_trans;
  string file_name;

  // 其他函式與邏輯
endclass
...
class case0_vseq extends uvm_sequence;
...
  virtual task body();
    my_transaction tr;
    read_file_seq seq0;
    drv1_seq seq1;
...
    `uvm_do_on_with(tr, p_sequencer.p_sqr0, {tr.pload.size == 1500;})
    `uvm_info("vseq", "send one longest packet on p_sequencer.p_sqr0", UVM_MEDIUM)

    seq0 = new("seq0");
    seq0.file_name = "data.txt";

    seq1 = new("seq1");

    fork
      seq0.start(p_sequencer.p_sqr0);
      seq1.start(p_sequencer.p_sqr1);
    join
...
  endtask
endclass
```
在 read_file_seq 中，需要一個字串的檔案名字，在手動啟動時可以指定檔案名字，但是 uvm_do 系列巨集無法實現這個功能，
因為 string 類型變數前不能使用 rand 修飾符。這就是手工啟動 sequence 的優勢。
在case0_vseq的定義中，一般都要使用uvm_declare_p_sequencer巨集。這個在前文已經講述過了，透過它可以引用sequencer的成
員變數。
回顧一下，為了解決 sequence 的同步，之前使用 send_over 這個全域變數的方式來解決。那麼在 virtual sequence 中是如何解決的
呢？事實上這個問題在 virtual sequence 中根本就不是個問題。由於 virtual sequence 的 body 是順序執行，所以只需要先產生一個最長
的包，產生完畢後再將其他的 sequence 啟動起來，沒有必要去刻意地同步。這只是 virtual sequence 強大的調度功能的一個小小的體
現。
virtual sequence 的使用可以減少 config_db 語句的使用。由於 config_db::set 函數的第二個路徑參數是字串，非常容易出錯，
所以減少 config_db 語句的使用可以降低出錯的機率。在上節中，使用了兩個 uvm_config_db 語句將兩個 sequence 送給了對應的 
sequencer 作為 default_sequence。假如驗證平台中的 sequencer 有多個，例如 10 個，那就需要寫 10 個 uvm_config_db 語句，這是一件很
令人厭煩的事。使用 virtual sequence 後可以將這 10 句只壓縮成一句：
```
function void my_case0::build_phase(uvm_phase phase);
…
  uvm_config_db#(uvm_object_wrapper)::set(this, "v_sqr.main_phase", "default_sequence", case0_vseq::type_id::get());
endfunction
```
virtual sequence 作為一種特殊的 sequence，也可以在其中啟動其他的 virtual sequence：
```
class case0_vseq extends uvm_sequence;
  …
  virtual task body();
    cfg_vseq cvseq;
  …
    `uvm_do(cvseq)
  …
  endtask
endclass
```
其中 cfg_vseq 是另外一個已經定義好的 virtual sequence。
