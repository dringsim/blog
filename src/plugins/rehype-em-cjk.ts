// https://lhcfl.github.io/blog/2026-06-22-%E4%BB%8E%E5%8D%9A%E5%AE%A2%E7%BE%8E%E5%8C%96%E5%BC%80%E5%A7%8B%E7%9A%84%E6%8E%92%E7%89%88%E5%AD%A6%E7%AC%94%E8%AE%B0/
import { toString as hastToString } from "hast-util-to-string";
import { visit } from "unist-util-visit";
import type { Root } from "hast";

export default function rehypeEmCJK() {
    return (tree: Root) => {
        visit(tree, "element", (node) => {
            if (["em"].includes(node.tagName)) {
                const textContent = hastToString(node);

                if (textContent.match(/[\p{Script=Hani}\p{Script=Hira}\p{Script=Kana}\p{Script=Hang}\p{Script=Bopo}]+/gu)) {
                    node.properties.className = node.properties.className ?? []
                    node.properties.className.push("em-cjk");
                }
            }
        });
    };
}
