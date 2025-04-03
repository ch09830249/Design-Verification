/*
    在一個規範化的 UVM 驗證平台中，driver 只負責驅動 transaction，而不負責產生 transaction。 sequence 機制有兩大組成部分，一是
    sequence，二是 sequencer
*/
class my_sequencer extends uvm_sequencer #(my_transaction); // uvm_sequencer 是一個參數化的類，其參數是 my_transaction，即此 sequencer 產生的 transaction 的類型。

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    `uvm_component_utils(my_sequencer)
endclass