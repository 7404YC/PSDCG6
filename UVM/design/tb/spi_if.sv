interface spi_if #(parameter CLK_DIV = 4)(
     input logic clk, 
     input logic rst_n
);

    // DUT interface signals
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

    // Clocking block for driver
    clocking drv_cb @(posedge clk);
        default input #1ns output #1ns;
        output start, tx_data;
        input  busy, done, rx_data;
    endclocking

    // Clocking block for monitor
    clocking mon_cb @(posedge clk);
        default input #1ns output #1ns;
        input start, tx_data, busy, done, rx_data;
    endclocking

    // Modports for separation of roles
    modport drv_mp  (clocking drv_cb, output sclk, mosi, cs_n, input miso);
    modport mon_mp (clocking mon_cb, input mosi, cs_n, sclk, miso);

endinterface
