// 定義基本測試與 sequence
class axi_test extends uvm_test;
    `uvm_component_utils(axi_test)

    axi_env env;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        env = axi_env::type_id::create("env", this);
    endfunction

    task run_phase(uvm_phase phase);
        axi_txn tr;

        phase.raise_objection(this);

        repeat (5) begin
            tr = axi_txn::type_id::create("tr");
            tr.id         = $urandom_range(0, 15);
            tr.addr       = $urandom();
            tr.burst_len  = 4;
            tr.burst_type = 2'b01;
            tr.burst_size = 3'b010; // 4 bytes
            tr.lock       = 0;
            tr.qos        = $urandom_range(0, 15);
            tr.is_write   = $urandom_range(0, 1);
            foreach (int i in tr.burst_len+1)
                tr.data.push_back($urandom());

            env.master_agent.sequencer.start_item(tr);
            env.master_agent.sequencer.finish_item(tr);
        end

        phase.drop_objection(this);
    endtask
endclass
