class axi_basic_seq extends uvm_sequence #(axi_txn);
    `uvm_object_utils(axi_basic_seq)

    function new(string name = "axi_basic_seq");
        super.new(name);
    endfunction

    task body();
        axi_txn tr;

        repeat (5) begin
            tr = axi_txn::type_id::create("tr");
            tr.id         = $urandom_range(0, 15);
            tr.addr       = $urandom();
            tr.burst_len  = 4;
            tr.burst_type = 2'b01;
            tr.burst_size = 3'b010;
            tr.burst_size = 3'b000;
            tr.lock       = 0;                          // Normal Access
            tr.qos        = $urandom_range(0, 15);
            tr.wstrb      = $urandom_range(0, 15);
            tr.is_write   = $urandom_range(0, 1);

            for (int i = 0; i <= tr.burst_len; i++)
                tr.data.push_back($urandom());

            `uvm_info(get_type_name(), "Sending txn", UVM_MEDIUM)

            start_item(tr);
            finish_item(tr);
        end
    endtask
endclass
