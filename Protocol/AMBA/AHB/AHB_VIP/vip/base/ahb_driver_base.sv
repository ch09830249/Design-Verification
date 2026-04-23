`ifndef AHB_DRIVER_BASE_SV
`define AHB_DRIVER_BASE_SV

class ahb_driver_base extends uvm_driver #(ahb_seq_item);
    `uvm_component_utils(ahb_driver_base)

    virtual ahb_interface       vif;

    ahb_seq_item                txn;

    uvm_active_passive_enum     agt_mode;

    function new ( string name = "ahb_driver_base", uvm_component parent );
        super.new(name, parent);
    endfunction

    virtual function bit is_idle();
        return 1;  // base 預設回傳 1
    endfunction

    function void build_phase ( uvm_phase phase );
        super.build_phase(phase);

        if ( !uvm_config_db #(virtual ahb_interface) :: get (this, "", "vif", vif) )
            `uvm_fatal("NOVIF", $sformatf("No interface set for %s.vif", get_full_name() ))

        if ( !uvm_config_db #(uvm_active_passive_enum) :: get (this, "", "agt_mode", agt_mode) )
            `uvm_fatal("NOAGTMODE", $sformatf("No agt_mode set for %s.agt_mode", get_full_name() ))
    endfunction
endclass

`endif
