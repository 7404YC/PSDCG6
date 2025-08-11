interface spi_if #(parameter CLK_DIV = 4) (
    input logic clk,
    input logic rst_n
);
    // Control and data signals
    logic        start;
    logic [7:0]  tx_data;
    logic [7:0]  rx_data;
    logic        busy;
    logic        done;

    // SPI interface pins
    logic        sclk;
    logic        mosi;
    logic        miso;
    logic        cs_n;

    // Clocking block for driving and sampling
    clocking cb @(posedge clk);
        input  rx_data, busy, done;
        output start, tx_data;
        input  sclk, miso;
        output mosi, cs_n;
    endclocking

endinterface
