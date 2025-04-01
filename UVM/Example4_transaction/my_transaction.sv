class my_transaction extends uvm_sequence_item; // my_transaction 的基底類別是 uvm_sequence_item

    rand bit[47:0] dmac;            // dmac 是 48bit 的乙太網路目的位址
    rand bit[47:0] smac;            // smac 是 48bit 的乙太網路來源位址
    rand bit[15:0] ether_type;      // ether_type 是乙太網路類型
    rand byte pload[];              // pload 是其攜帶資料的大小
    rand bit[31:0] crc;

    constraint pload_cons {     // pload 大小被限制在 46～1500 byte
        pload.size >= 46;
        pload.size <= 1500;
    }

    function bit[31:0] calc_crc();
        return 32'h0;
    endfunction

    function void post_randomize();
        crc = calc_crc;             // 當某個類別的實例的 randomize 函數被呼叫後，post_randomize 會緊接著無條件地被調用。
    endfunction

    `uvm_object_utils(my_transaction)
    /*
    使用了 uvm_object_utils。從本質上來說，my_transaction 與 my_driver 是有差別的，在整個模擬期間，my_driver 是一直存在的，
    my_transaction 不同，它有生命週期。它在模擬的某一時間產生，經過 driver 驅動，再經過 reference model 處理，最終由scoreboard比較完成後，
    其生命週期就結束了。一般來說，這種類都是派生自 uvm_object 或 uvm_object 的衍生類，uvm_sequence_item 的祖先就是 uvm_object。 
    */

    function new(string name = "my_transaction");
        super.new(name);
    endfunction

endclass