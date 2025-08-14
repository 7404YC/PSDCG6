// T013: Ensure MOSI only changes on rising sclk edges
property T013;
	@(posedge clk)
	disable iff (!rst_n)
		(
			// When there is no rising sclk events, but detect mosi changes, this will flag error
			(mosi !== $past(mosi) && !($rose(sclk))) |-> 0
		);
endproperty
ASSERT_T013: assert property (T013)
	else $error("ASSERT ", $sformatf("Error T013"));

// T014: Ensure MISO only sampled in failing sclk edges
// YK: Drop this, cover in scoreboard

// T018: When the SPI is idle, ensure no sclk events and cs_n is pulled high.
property T018;
	@(posedge clk)
	disable iff (!rst_n)
		(
			(state == 0 && start == 0) |->
			(
				sclk == 0 &&
				cs_n == 1
			)
		);
endproperty
ASSERT_T018: assert property (T018)
	else $error("ASSERT ", $sformatf("Error T018"));

// T020: All outputs are set to default/reset values when rst_n = 0, except mosi
// Reason to use always_comb is because the reset is asynchronous to the clock, so we cannot use property which is sensitive to the clock
always_comb begin
	if (rst_n == 1'b0) begin

	ASSERT_T020:
		assert final (
					(busy == 1'b0) &&
					(done == 1'b0) &&
					(rx_data == 8'b0) &&
					(sclk == 1'b0) &&
					(cs_n == 1'b1)
				)
		else $error("ASSERT ", $sformatf("Error T020"));
	end
end

