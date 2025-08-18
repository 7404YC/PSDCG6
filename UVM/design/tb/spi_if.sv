interface spi_if #(parameter CLK_DIV = 4)(
);

    // DUT interface signals
	logic		 clk;
	logic		 rst_n;
    logic        start;
    logic [7:0]  tx_data;
    logic [7:0]  rx_data;
    logic        busy;
    logic        done;

    // SPI physical interface
    logic        sclk;
    logic        mosi;
    logic        miso;
    logic        cs_n;

	// Probe Internal Signal
	logic		state;
    logic [7:0] rx_reg;

    // Clocking block for driver
    clocking drv_cb @(posedge clk);
        default input #1ns output #1ns;
        output start, tx_data;
        input  busy, done, rx_data;
    endclocking

    // simulated reversed clock signal 
    logic       isclk; 
    always @(edge sclk) begin 
        isclk = ~sclk;
    end

    // Modports for separation of roles
    modport drv_mp  (clocking drv_cb, output sclk, mosi, cs_n, input miso, rst_n);
    modport mon_mp (input clk, start, tx_data, busy, done, rx_data, mosi, cs_n, sclk, miso, rst_n, isclk);

	`include "spi_ass_xy.svh"
	`include "spi_ass_yc.svh"
	`include "spi_ass_yk.svh"

endinterface
