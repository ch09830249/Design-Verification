class my_transaction extends uvm_sequence_item;

    rand bit[47:0] dmac;
    rand bit[47:0] smac;
    rand bit[15:0] ether_type;
    rand byte pload[];
    rand bit[31:0] crc;

    constraint pload_cons {
        pload.size >= 20;
        pload.size <= 1500;
    }

    function bit[31:0] calc_crc();
        return 32'h0;
    endfunction

    function void post_randomize();
        crc = calc_crc();
    endfunction
    
    function void my_print(string name);
        $display("======================= Print Transaction (%s)=======================", name);
        $display("dmac: %0h", dmac);
        $display("smac: %0h", smac);
        $display("ether_type: %0h", ether_type);
        foreach (pload[i]) begin
            $display("pload[%0d] = %0h", i, pload[i]);
        end
        $display("crc: %0h", crc);
        $display("==============================================");
    endfunction

    // 這裡多實現兩個 my_transaction 的複製
    function void my_copy(my_transaction tr);
        if(tr == null)
            `uvm_fatal("my_transaction", "tr is null!!!!")
        dmac = tr.dmac;
        smac = tr.smac;
        ether_type = tr.ether_type;
        pload = new[tr.pload.size()];
        for(int i = 0; i < pload.size(); i++) begin
            pload[i] = tr.pload[i];
        end
        crc = tr.crc;
    endfunction

    `uvm_object_utils(my_transaction)

    function new(string name = "my_transaction");
        super.new(name);
    endfunction

endclass
