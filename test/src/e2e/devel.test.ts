// Copyright 2019 Kodebox, Inc.
// This file is part of CodeChain.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as
// published by the Free Software Foundation, either version 3 of the
// License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Affero General Public License for more details.
//
// You should have received a copy of the GNU Affero General Public License
// along with this program.  If not, see <https://www.gnu.org/licenses/>.

import { expect } from "chai";
import "mocha";
import CodeChain from "../helper/spawn";

describe("development RPCs", function() {
    let node: CodeChain;
    before(async function() {
        node = new CodeChain({ argv: ["--force-sealing"] });
        await node.start();
    });

    async function getLastTermEnd(): Promise<[number, number] | null> {
        return await node.sdk.rpc.sendRpcRequest("devel_lastTermEnd", []);
    }

    it("should end term every 5 blocks", async function() {
        const testRanges = [
            {
                from: 0,
                to: 3,
                lastTermEnd: null
            },
            {
                from: 4,
                to: 8,
                lastTermEnd: [0, 4]
            },
            {
                from: 9,
                to: 13,
                lastTermEnd: [1, 9]
            }
        ];

        for (const { from, to, lastTermEnd } of testRanges) {
            for (let i = from; i <= to; i++) {
                expect(
                    await node.sdk.rpc.chain.getBestBlockNumber()
                ).to.be.equal(i);
                expect(await getLastTermEnd()).to.be.deep.equal(lastTermEnd);
                await node.sdk.rpc.devel.startSealing();
            }
        }
    });

    after(async function() {
        await node.clean();
    });
});
