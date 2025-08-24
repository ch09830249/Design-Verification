/*
    只有在 sequencer 的幫助下，sequence 產生出的 transaction 才能最終送給 driver；同樣，sequencer 只有在 sequence 出現的情況下才能體現其價
    值，如果沒有 sequence，sequencer 就幾乎沒有任何作用。 sequence 就像是彈夾，裡面的子彈是 transaction，而 sequencer 是一把槍

    sequencer 是一個 uvm_component，而 sequence 是一個 uvm_object。與 my_transaction 一樣，sequence 也有其生命週期。它的生命週期比 my_transaction 要更長一些，
    其內的 transaction 全部發送完畢後，它的生命週期也就結束了。這就好比一個彈夾，裡面的子彈用完後就沒有任何意義了。
*/
class my_sequence extends uvm_sequence #(my_transaction);   // 每一個sequence都應該派生自uvm_sequence，並且在定義時指定要產生的transaction的類型
    my_transaction m_trans;

    function new(string name = "my_sequence");
        super.new(name);
    endfunction

    virtual task body();    // 當一個 sequence 啟動之後，會自動執行 body 中的程式碼
        int num = 0;
        repeat (10) begin
            num = num + 1;
            `uvm_info("my_sequence", $sformatf("transaction: %0d", num), UVM_LOW)
            `uvm_do(m_trans)
            // m_trans = my_transaction::type_id::create("m_trans");  // 透過 factory 機制實例化 transaction
            // start_item(m_trans);                                   // 對 transaction 設置
            // if(!m_trans.randomize())                               // 隨機化 transaction
            //     `uvm_error("", "Randomize failed")
            // finish_item(m_trans);
        end
        #1000;  // 這是為了讓最後一筆 tr 順利流過 driver => monitor => model => scoreboard
    endtask

    `uvm_object_utils(my_sequence)  // 一個 sequence 應該使用 uvm_object_utils 巨集註冊到 factory 中
endclass


/*
    uvm_do
        1. 創建一個 my_transaction 的實例 m_trans
        2. 將其隨機化
        3. 最終將其送給 sequencer。
        
    如果不使用 uvm_do 宏，也可以直接使用 start_item 與 finish_item 的方式產生 transaction。

    一個 sequence 在向 sequencer 發送 transaction 前，要先向 sequencer 發送一個請求，sequencer 把這個請求放在一個仲裁佇列中。作
    為 sequencer，它需做兩件事：
        第一，偵測仲裁佇列裡是否有某個 sequence 發送 transaction 的請求
        ​​第二，偵測 driver 是否申請 transaction

    1）如果仲裁佇列裡有發送請求，但是 driver 沒有申請 transaction，那麼 sequencer 將會一直處於等待 driver 的狀態，直到 driver 申
       請新的 transaction。此時，sequencer 同意 sequence 的發送請求，sequence 在得到 sequencer 的批准後，產生出一個 transaction 並交給
       sequencer，後者把這個 transaction 交給 driver。
    2）如果仲裁佇列中沒有發送請求，但是 driver 向 sequencer 申請新的 transaction，那麼 sequencer 將會處於等待 sequence 的狀態，
       一直到有 sequence 遞交送請求，sequencer 馬上同意這個請求，sequence 產生 transaction 並交給 sequencer，最終 driver 獲得這個
       transaction。
    3）如果仲裁佇列中有發送請求，同時 driver 也在向 sequencer 申請新的 transaction，那麼將會同意發送請求，sequence 產生
       transaction 並交給 sequencer，最後 driver 獲得這個 transaction。
*/
