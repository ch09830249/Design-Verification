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
