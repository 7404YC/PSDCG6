`include "spi_if.sv"
`include "spi.sv"

    `include "spi_accessor.sv" // Accessor module
module spi_tb;
    import uvm_pkg::*;
    `include "uvm_macros.svh"

    // $time is a built-in system function
    initial $display(">>>>>>>> SIM TIME START: %0t", $time);
    final   $display(">>>>>>>> SIM TIME END  : %0t", $time);

    // Include all required files
    `include "spi_tran.sv"
    `include "spi_seq.sv"       // Sequence class
    `include "spi_seq_sanity.sv"       // Sequence class
    `include "spi_seq_b2b.sv"       // Sequence class
    `include "spi_sqr.sv"       // Sequencer class
    `include "spi_drv.sv"       // Driver class
    `include "spi_mon0.sv"       // Monitor class
    `include "spi_mon1.sv"       // Monitor class
    `include "spi_mon2.sv"       // Monitor class
    `include "spi_agt0.sv"       // Agent0 class
    `include "spi_agt1.sv"       // Agent1 class
    `include "spi_scb.sv"       // Scoreboard class
    `include "spi_cov.sv"		// Coverage class
    `include "spi_env.sv"       // Env class
    `include "spi_test.sv"      // Test class
    `include "spi_test_sanity.sv"      // Test class
    `include "spi_test_b2b.sv"      // Test class

    spi_if spi_if();

	integer ctt;

    // Initialization 
    initial begin
        spi_if.clk = 0;
		spi_if.rst_n = 0;
		spi_if.start = 0;
		spi_if.tx_data = '0;
    end

	// Clock driving
	always begin
        #5 spi_if.clk <= ~spi_if.clk;
	end

    // Instantiate the DUT
    spi #(.CLK_DIV(4)) dut (
		.clk (spi_if.clk),
		.rst_n (spi_if.rst_n),
		.start (spi_if.start),
		.tx_data (spi_if.tx_data),
		.rx_data (spi_if.rx_data),
		.busy (spi_if.busy),
		.done (spi_if.done),

		.sclk (spi_if.sclk),
		.mosi (spi_if.mosi),
		.miso (spi_if.miso),
		.cs_n (spi_if.cs_n)
    );

    // Instantiate accessor module
    bind spi peek_dut peek_inst(.vif(spi_if), .rx_reg_pd(dut.rx_reg));

	// Probe Internal Signal
	assign spi_if.state = dut.state;

    // Constants
    bit [7:0] SLAVE_RESET_RESPONSE = 'hB9;
    int slave_reset_response = SLAVE_RESET_RESPONSE;

    // Simple SPI slave model for testing
    logic [7:0] slave_rx_data;
    logic [7:0] slave_tx_data;

    // For aborting driver and scoreboard
    bit monitor0_abort = 0;
    bit monitor1_abort = 0;

    // uvm config db 
    initial begin 
        uvm_config_db#(logic [7:0])::set(null, "*", "slave_rx_data", slave_rx_data);
		uvm_config_db#(logic [7:0])::set(null, "*", "slave_tx_data", slave_tx_data);
		uvm_config_db#(logic [7:0])::set(null, "*", "slave_reset_resp", slave_reset_response);
        uvm_config_db#(bit)::set(null, "*", "mon0_abort", monitor0_abort);
        uvm_config_db#(bit)::set(null, "*", "mon1_abort", monitor1_abort);
    end

	logic [31:0] int_counter = 1;

    always @(posedge spi_if.sclk or negedge spi_if.rst_n or posedge spi_if.cs_n) begin
        if (!spi_if.rst_n) begin
            slave_rx_data <= 8'h00;
            spi_if.miso <= 1'b0;
			int_counter <= '0;
            slave_tx_data <= SLAVE_RESET_RESPONSE;
        end
        else if (spi_if.cs_n) begin
            spi_if.miso <= 1'b0;
            slave_tx_data <= SLAVE_RESET_RESPONSE;

            `uvm_info("SLV-RLD", $sformatf("RX_REG=0x%2h \(%8b\), TX_REG=0x%2h \(%8b\)",
                                               slave_rx_data, slave_rx_data, slave_tx_data, slave_tx_data), UVM_MEDIUM)
        end
        else begin
                // Shift in MOSI on rising edge
                slave_rx_data <= {slave_rx_data[6:0], spi_if.mosi};

                // Update MISO immediately for next bit
                spi_if.miso <= slave_tx_data[7];
                slave_tx_data <= {slave_tx_data[6:0], 1'b0};

                `uvm_info("SLV", $sformatf("RX_REG=0x%2h \(%8b\), TX_REG=0x%2h \(%8b\)",
                                           slave_rx_data, slave_rx_data, slave_tx_data, slave_tx_data), UVM_MEDIUM)
        end
    end



    // UVM config db setting & test launch
    initial begin
        uvm_config_db#(virtual spi_if.drv_mp)::set(null, "*drv*", "vif", spi_if);
        uvm_config_db#(virtual spi_if.mon_mp)::set(null, "*mon*", "vif", spi_if);
        uvm_config_db#(virtual spi_if)::set(null, "*", "vif", spi_if);

		if ($test$plusargs("SANITY_TEST") || $test$plusargs("SANITY_TEST_RESET_DURING_TRANS")) begin
	        run_test("spi_test_sanity");
		end
		else if ($test$plusargs("B2B_TEST") || $test$plusargs("B2B_TEST_RESET_DURING_TRANS")) begin
	        run_test("spi_test_b2b");
		end	
		else begin
			run_test();
		end
    end

    // Simulation timeout 
    //initial begin 
	//	ctt = 0;
    //    if($value$plusargs("CUSTOM_TEST_TIMEOUT=%0d", ctt)) begin
    //        #ctt;
    //        $finish;
    //    end else begin 
    //        #5000; // TODO: adjust arbitrary value to suitable
    //        $finish;
    //    end
    //end 

    // Waveform generation 
    initial begin
        $fsdbDumpfile("spi_sim.fsdb");
        $fsdbDumpSVA(0, spi_tb);
        $fsdbDumpvars(0, spi_tb);
    end
endmodule
