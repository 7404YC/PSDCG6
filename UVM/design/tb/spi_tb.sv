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

    // Instantiate the DUT
    spi #(.CLK_DIV(4)) dut (
    ...
    ...
    );

    // Constants
    bit [7:0] SLAVE_RESET_RESPONSE = 8'hB9;
    int slave_reset_response = SLAVE_RESET_RESPONSE;

    // Simple SPI slave model for testing
    logic [7:0] slave_rx_data;
    logic [7:0] slave_tx_data = SLAVE_RESET_RESPONSE;
    uvm_config_db#(int)::set(null, "*", "slave_reset_response", slave_reset_response);

    always @(posedge spi_if0.sclk or negedge spi_if0.rst_n or posedge spi_if0.cs_n) begin
        if (!spi_if0.rst_n) begin
            slave_rx_data <= 8'h00;
            spi_if0.miso <= 1'b0;
            slave_tx_data <= SLAVE_RESET_RESPONSE;
        end
        else if (spi_if0.cs_n) begin
            spi_if0.miso <= 1'b0;
            slave_tx_data <= SLAVE_RESET_RESPONSE;

            `uvm_info("SLV-RLD", $sformatf("RX_REG=0x%2h \(%8b\), TX_REG=0x%2h \(%8b\)",
                                               slave_rx_data, slave_rx_data, slave_tx_data, slave_tx_data), UVM_MEDIUM)
        end
        else begin
                // Shift in MOSI on rising edge
                slave_rx_data <= {slave_rx_data[6:0], spi_if0.mosi};

                // Update MISO immediately for next bit
                spi_if0.miso <= slave_tx_data[7];
                slave_tx_data <= {slave_tx_data[6:0], 1'b0};

                `uvm_info("SLV", $sformatf("RX_REG=0x%2h \(%8b\), TX_REG=0x%2h \(%8b\)",
                                           slave_rx_data, slave_rx_data, slave_tx_data, slave_tx_data), UVM_MEDIUM)
        end
    end



    // UVM config db setting & test launch
    initial begin
        uvm_config_db#(virtual bus_ctrl_if)::set(null, "*drv*", "vif", bus_if);
        uvm_config_db#(virtual bus_ctrl_if)::set(null, "*mon*", "vif", bus_if);
        uvm_config_db#(virtual spi_ctrl_if)::set(null, "*", "vif", spi_if);
        run_test("spi_test");
    end

    // Simulation timeout 
    initial begin 
        if($value$plusargs("CUSTOM_TEST_TIMEOUT=%0d", ctt)) begin
            #ctt;
            $finish;
        else begin 
            #5000; // TODO: adjust arbitrary value to suitable
            $finish;
        end
    end 

    // Waveform generation 
    initial begin
        $fsdbDumpfile("spi_sim.fsdb");
        $fsdbDumpSVA(0, spi_tb);
        $fsdbDumpvars(0, spi_tb);
    end
endmodule