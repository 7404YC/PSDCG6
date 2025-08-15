module peek_dut(
	spi_if vif, 
	input logic [7:0] rx_reg_pd,
	input state_pd
);
    assign vif.rx_reg = rx_reg_pd;
	assign vif.state = state_pd;
endmodule

// xt
