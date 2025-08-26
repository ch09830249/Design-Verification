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
    
    function void print_tr();
        $display("======================= Print Transaction =======================");
        $display("dmac: %h", dmac);
        $display("smac: %h", smac);
        $display("ether_type: %h", ether_type);
        foreach (pload[i]) begin
            $display("pload[%0d] = %h", i, pload[i]);
        end
        $display("crc: %h", crc);
        $display("==============================================");
    endfunction

    `uvm_object_utils(my_transaction)

    function new(string name = "my_transaction");
        super.new(name);
    endfunction

endclass
