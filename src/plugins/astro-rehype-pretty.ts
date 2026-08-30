// modified from https://github.com/expressive-code/expressive-code/tree/main/packages/astro-expressive-code/src
import type { AstroIntegration } from "astro";
import rehypePrettyCode from "rehype-pretty-code";
import { expressiveCodeConfig } from "../config/";

type ConfigSetupHookArgs = Parameters<NonNullable<AstroIntegration["hooks"]["astro:config:setup"]>>[0];

export default function astroRehypePretty() {
	return {
		name: "astro-rehype-pretty",
		hooks: {
			"astro:config:setup": async (args: unknown) => {
				const { config: astroConfig } = args as ConfigSetupHookArgs;

				const markdownProcessorOptions = astroConfig.markdown.processor.options as { rehypePlugins: unknown[] };
				markdownProcessorOptions.rehypePlugins.push(() => rehypePrettyCode(
					{
						theme: {
							light: expressiveCodeConfig.lightTheme,
							dark: expressiveCodeConfig.darkTheme,
						},
					}
				))
			},
		},
	} satisfies AstroIntegration;
}
