`include "spi_if.sv"
`include "spi.sv"

module spi_tb;
    import uvm_pkg::*;
    `include "uvm_macros.svh"

    // $time is a built-in system function
    initial $display(">>>>>>>> SIM TIME START: %0t", $time);
    final   $display(">>>>>>>> SIM TIME END  : %0t", $time);

    // Include all required files
    `include "spi_tran.sv"
    `include "spi_seq.sv"       // Sequence class
    `include "spi_sqr.sv"       // Sequencer class
    `include "spi_drv.sv"       // Driver class
    `include "spi_mon.sv"       // Monitor class
    `include "spi_agt.sv"       // Agent class
    `include "spi_scb.sv"       // Scoreboard class
    `include "spi_cov.sv"		// Coverage class
    `include "spi_env.sv"       // Env class
    `include "spi_test.sv"      // Test class

    spi_if spi_if();

    spi dut(

    );

    // Clock driving 
    initial begin
        spi_if.clk_tb = 0;
        forever #5 spi_if.clk_tb = ~spi_if.clk_tb;
    end

    // Value initialization
    initial begin

    end

    // UVM config db setting & test launch
    initial begin
        uvm_config_db#(virtual bus_ctrl_if)::set(null, "*drv*", "vif", bus_if);
        uvm_config_db#(virtual bus_ctrl_if)::set(null, "*mon*", "vif", bus_if);
        uvm_config_db#(virtual spi_ctrl_if)::set(null, "*", "vif", spi_if);
        run_test("spi_test");
    end

    // Waveform generation 
    initial begin
        $fsdbDumpfile("spi_sim.fsdb");
        $fsdbDumpSVA(0, spi_tb);
        $fsdbDumpvars(0, spi_tb);
    end
endmodule