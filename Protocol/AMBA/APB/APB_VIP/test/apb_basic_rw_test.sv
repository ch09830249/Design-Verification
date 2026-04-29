`ifndef APB_BASIC_RW_TEST_SV
`define APB_BASIC_RW_TEST_SV

class apb_basic_rw_test extends uvm_test;
    `uvm_component_utils(apb_basic_rw_test)

    apb_env                     env;
    apb_master_seq              mst_seq;

    function new ( string name = "apb_basic_rw_test", uvm_component parent );
        super.new(name, parent);
    endfunction

    function void build_phase ( uvm_phase phase );
        super.build_phase(phase);
        env = apb_env :: type_id :: create ("env", this);
    endfunction

    virtual task run_phase ( uvm_phase phase );
        phase.raise_objection(this);

        mst_seq = apb_master_seq :: type_id :: create("mst_seq");
        mst_seq.start(env.agt_mst.seqr);
        repeat(10) @ (posedge env.vif.PCLK);  // ensure the last transfer done

        phase.drop_objection(this);
    endtask

    function void end_of_elaboration_phase (uvm_phase phase);
        super.end_of_elaboration_phase(phase);
        uvm_top.print_topology();
        uvm_factory::get().print();
    endfunction
endclass

`endif
