`ifndef AXI_BASIC_RW_TEST_SV
`define AXI_BASIC_RW_TEST_SV

class axi_basic_rw_test extends uvm_test;
    `uvm_component_utils(axi_basic_rw_test)

    axi_env                     env;
    axi_master_seq              mst_seq;

    function new(string name = "axi_basic_rw_test", uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        env = axi_env::type_id::create("env", this);
    endfunction

    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);

        mst_seq = axi_master_seq::type_id::create("mst_seq");
        mst_seq.start(env.agt_mst.seqr);
        repeat(1000000) @(posedge env.vif.ACLK);  // ensure the last transfer done

        phase.drop_objection(this);
    endtask

    function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);
        uvm_top.print_topology();
        uvm_factory::get().print();
    endfunction

endclass

`endif
