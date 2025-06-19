/*
    在這個容器類別中實例化 driver、monitor、reference model 和 scoreboard 等。在調用
    run_test 時，傳遞的參數不再是 my_driver，而是這個容器類，也就是讓 UVM 自動建立這個容器類別的實例。在UVM中，這個容器類別稱為 uvm_env
*/
class my_env extends uvm_env;

    my_driver drv;

    function new(string name = "my_env", uvm_component parent);
        super.new(name, parent);
    endfunction

    /*
        在 UVM 的樹狀結構中，build_phase 的執行遵照從樹根到樹葉的順序，也就是先執行 my_env 的 build_phase，再執行 my_driver 的 build_phase。
        當把整棵樹的 build_phase 都執行完畢後，再執行後面的 phase。
    */
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        drv = my_driver::type_id::create("drv", this);  // factory 機制所帶來的獨特的實例化方式。只有使用 factory 機制註冊過的類別才能使用這種方式實例化
    endfunction

    `uvm_component_utils(my_env)    // 容器類別在模擬中也是一直存在的，使用 uvm_component_utils 宏來實現 factory 的註冊。

endclass

/*
第一個參數是實例的名字，第二個則是 parent。由於 my_driver 在 uvm_env 中實例化，所以 my_driver
的父結點（parent）就是 my_env。透過 parent 的形式，UVM 建立起了樹狀的組織結構。在這種樹狀的組織結構中，由 run_test 建立
的實例是樹根（這裡是 my_env），而樹根的名字是固定的，為 uvm_test_top；在樹根之後會生長出枝
葉（這裡只有 my_driver），長出枝葉的過程需要在 my_env 的 build_phase 中手動實作。無論是樹根還是樹葉，都必須由
uvm_component 或其衍生類別繼承而來。
*/
